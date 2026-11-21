import Breakdown.Cert.Nodes
import Breakdown.Cert.TestPairing
import Breakdown.Cert.Convection
import Breakdown.Weak.AdvectionByParts
import Breakdown.Weak.SliceEmbedding
import Breakdown.Weak.PairingVelocity
import Breakdown.Weak.ZeroGradient
import Breakdown.Weak.GradientFreqTr

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.HeldWeakEquation

def transportTest (P : ℝ) (φ : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  -(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2 - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2

def barPart (P : ℝ) (W φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  sigmaSimilarityIntegrand P W (fun σ y => fderiv ℝ (W σ) y) φ z

def linPart (P : ℝ) (v : VelField) (G : GradField) (φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  inner ℝ (v z.1 z.2) (transportTest P φ z) + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)

def crossPart (W v φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  -(∑ i : Fin 3, (W z.1 z.2) i * inner ℝ (v z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i)))
    - ∑ i : Fin 3, (v z.1 z.2) i * inner ℝ (W z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i))

def quadPart (v φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  -∑ i : Fin 3, (v z.1 z.2) i * inner ℝ (v z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i))

theorem integrand_split (P : ℝ) (W v : ℝ → Space → Space) (G : GradField)
    (φ : ℝ → Space → Space) (z : ℝ × Space) :
    sigmaSimilarityIntegrand P (fun σ y => W σ y + v σ y) (fun σ y => fderiv ℝ (W σ) y + G σ y) φ z =
      barPart P W φ z + linPart P v G φ z + crossPart W v φ z + quadPart v φ z := by
  simp only [sigmaSimilarityIntegrand, barPart, linPart, crossPart, quadPart, transportTest, matInner,
    ContinuousLinearMap.add_apply, PiLp.add_apply, inner_add_left, inner_sub_right,
    inner_smul_right, Fin.sum_univ_three]
  ring

theorem defect_split {k : ℕ} (P : ℝ) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (b : Fin k → ℝ → Space → Space) (m : Fin k → ℝ) (σ : ℝ) (y : Space) :
    defectField P W q b m σ y = defectField P W q b 0 σ y + ∑ i, m i • b i σ y := by
  simp only [defectField, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  abel

theorem slice_fderiv_eq_joint {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) (z : ℝ × Space) :
    fderiv ℝ (φ z.1) z.2 =
      (fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hΦ : DifferentiableAt ℝ (fun w : ℝ × Space => φ w.1 w.2) (z.1, z.2) :=
    (hφ.1.differentiable (by simp)) _
  have h := hΦ.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  exact h.fderiv

theorem slice_deriv_eq_joint {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) (z : ℝ × Space) :
    deriv (fun s => φ s z.2) z.1 =
      fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2) z (ContinuousLinearMap.inl ℝ ℝ Space 1) := by
  have hΦ : DifferentiableAt ℝ (fun w : ℝ × Space => φ w.1 w.2) (z.1, z.2) :=
    (hφ.1.differentiable (by simp)) _
  have h := hΦ.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  exact h.hasDerivAt.deriv

theorem test_fderiv {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2) ∧
    HasCompactSupport (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2) := by
  have he : (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2) =
      (fun L : (ℝ × Space) →L[ℝ] Space => L.comp (ContinuousLinearMap.inr ℝ ℝ Space)) ∘
        fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2) := funext (slice_fderiv_eq_joint hφ)
  have hc : Continuous (fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2)) :=
    hφ.1.continuous_fderiv (by simp)
  rw [he]
  exact ⟨hc.clm_comp continuous_const,
    (hφ.2.1.fderiv (𝕜 := ℝ)).comp_left (by simp)⟩

theorem test_deriv {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Continuous (fun z : ℝ × Space => deriv (fun s => φ s z.2) z.1) ∧
    HasCompactSupport (fun z : ℝ × Space => deriv (fun s => φ s z.2) z.1) := by
  have he : (fun z : ℝ × Space => deriv (fun s => φ s z.2) z.1) =
      (fun L : (ℝ × Space) →L[ℝ] Space => L (ContinuousLinearMap.inl ℝ ℝ Space 1)) ∘
        fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2) := funext (slice_deriv_eq_joint hφ)
  have hc : Continuous (fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2)) :=
    hφ.1.continuous_fderiv (by simp)
  rw [he]
  exact ⟨hc.clm_apply continuous_const,
    (hφ.2.1.fderiv (𝕜 := ℝ)).comp_left (by simp)⟩

theorem velocity_slice_bound {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (R : ℝ) :
    ∀ᵐ σ : ℝ, ∫⁻ y in Metric.closedBall (0 : Space) R, ‖v σ y‖ₑ ^ 2 ≤
      (‖(velocity : X →L[ℝ] L6R)‖ₑ * supGrad u *
        volume (Metric.closedBall (0 : Space) R) ^ (1 / 3 : ℝ)) ^ 2 := by
  have hsup : ∀ᵐ σ : ℝ, ‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ₑ ≤ supGrad u := by
    have h0 : ∀ᵐ t : TimeCircle, ‖gradPart ((u : TimeCircle → XBar) t)‖ₑ ≤ supGrad u := by
      have := ae_le_eLpNormEssSup (μ := (volume : Measure TimeCircle))
        (f := fun t => gradPart ((u : TimeCircle → XBar) t))
      simpa [supGrad, eLpNorm_exponent_top] using this
    exact (ae_coe_iff (fun t => ‖gradPart ((u : TimeCircle → XBar) t)‖ₑ ≤ supGrad u)).1 h0
  filter_upwards [hsup, hr.velocity_eq] with σ hs hv
  have hg : AEStronglyMeasurable
      (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space)
      (volume.restrict (Metric.closedBall (0 : Space) R)) :=
    (Lp.aestronglyMeasurable _).restrict
  have h1 : ∫⁻ y in Metric.closedBall (0 : Space) R, ‖v σ y‖ₑ ^ 2 =
      eLpNorm (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) 2
        (volume.restrict (Metric.closedBall (0 : Space) R)) ^ 2 := by
    rw [JointRepresentativeInternal.sq_eLpNorm_two]
    exact lintegral_congr_ae (ae_restrict_of_ae (hv.mono fun y hy => by simp only [hy]))
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := 6) (by norm_num) hg
  have h3 : eLpNorm (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) 6
      (volume.restrict (Metric.closedBall (0 : Space) R)) ≤
      ‖(velocity : X →L[ℝ] L6R)‖ₑ * supGrad u := by
    calc eLpNorm (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) 6
          (volume.restrict (Metric.closedBall (0 : Space) R)) ≤
          eLpNorm (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) 6
            volume := eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = ‖velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))‖ₑ := (Lp.enorm_def _).symm
      _ ≤ _ := ContinuousLinearMap.le_opENorm_of_le _ hs
  have e : (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) = (1 / 3 : ℝ) := by
    simp only [ENNReal.toReal_ofNat]
    norm_num
  have h4 : eLpNorm (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) 2
      (volume.restrict (Metric.closedBall (0 : Space) R)) ≤
      ‖(velocity : X →L[ℝ] L6R)‖ₑ * supGrad u * volume (Metric.closedBall (0 : Space) R) ^ (1 / 3 : ℝ) := by
    have e2 : (volume.restrict (Metric.closedBall (0 : Space) R)) univ ^
        (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) =
        volume (Metric.closedBall (0 : Space) R) ^ (1 / 3 : ℝ) := by
      rw [Measure.restrict_apply_univ (Metric.closedBall (0 : Space) R), e]
    refine h2.trans (le_of_eq_of_le (congrArg _ e2) ?_)
    gcongr
  rw [h1]
  exact pow_le_pow_left' h4 2

theorem velocity_box_sq {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) (M R : ℝ) :
    IntegrableOn (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2)
      (Icc (-M) M ×ˢ Metric.closedBall (0 : Space) R) := by
  have hCt : (‖(velocity : X →L[ℝ] L6R)‖ₑ * supGrad u *
      volume (Metric.closedBall (0 : Space) R) ^ (1 / 3 : ℝ)) ^ 2 < ⊤ := by
    refine ENNReal.pow_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top hsup) ?_)
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_closedBall_lt_top).ne
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume := hr.measurable_velocity
  have hA : AEMeasurable (fun z : ℝ × Space => ‖v z.1 z.2‖ₑ ^ 2)
      ((volume.restrict (Icc (-M) M)).prod (volume.restrict (Metric.closedBall (0 : Space) R))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hm.enorm.pow_const 2).restrict
  refine ⟨(hm.norm.pow 2).restrict, ?_⟩
  show ∫⁻ z in Icc (-M) M ×ˢ Metric.closedBall (0 : Space) R, ‖‖v z.1 z.2‖ ^ 2‖ₑ < ⊤
  have e1 : ∀ z : ℝ × Space, ‖‖v z.1 z.2‖ ^ 2‖ₑ = ‖v z.1 z.2‖ₑ ^ 2 := fun z => by
    rw [Real.enorm_of_nonneg (sq_nonneg _)]
    exact Internal.Convection.ofReal_norm_sq_eq _
  simp only [e1]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hA]
  calc ∫⁻ σ in Icc (-M) M, ∫⁻ y in Metric.closedBall (0 : Space) R, ‖v (σ, y).1 (σ, y).2‖ₑ ^ 2
        ≤ ∫⁻ σ in Icc (-M) M, (‖(velocity : X →L[ℝ] L6R)‖ₑ * supGrad u *
            volume (Metric.closedBall (0 : Space) R) ^ (1 / 3 : ℝ)) ^ 2 :=
        lintegral_mono_ae (ae_restrict_of_ae (velocity_slice_bound hr R))
    _ = (‖(velocity : X →L[ℝ] L6R)‖ₑ * supGrad u *
            volume (Metric.closedBall (0 : Space) R) ^ (1 / 3 : ℝ)) ^ 2 *
          volume (Icc (-M) M) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top hCt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

theorem velocity_local {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) {ψ : ℝ × Space → Space}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (ψ z)) ∧
    ∀ i : Fin 3, Integrable (fun z : ℝ × Space => (v z.1 z.2) i * inner ℝ (v z.1 z.2) (ψ z)) := by
  obtain ⟨Cψ, hCψ⟩ := hψ.bounded_above_of_compact_support hψc
  obtain ⟨r, hr0⟩ := isBounded_iff_forall_norm_le.1 hψc.isCompact.isBounded
  have hK : MeasurableSet (Icc (-r) r ×ˢ Metric.closedBall (0 : Space) r) :=
    measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hKf : volume (Icc (-r) r ×ˢ Metric.closedBall (0 : Space) r) < ⊤ :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : Space) r)).measure_lt_top
  have hsq := velocity_box_sq hr hsup r r
  have hdom : Integrable ((Icc (-r) r ×ˢ Metric.closedBall (0 : Space) r).indicator
      fun z : ℝ × Space => Cψ * (1 + ‖v z.1 z.2‖ ^ 2)) := by
    refine IntegrableOn.integrable_indicator ?_ hK
    exact ((integrableOn_const hKf.ne).add hsq).const_mul Cψ
  have hz : ∀ z, z ∉ Icc (-r) r ×ˢ Metric.closedBall (0 : Space) r → ψ z = 0 := by
    intro z hzK
    apply image_eq_zero_of_notMem_tsupport
    intro hzt
    apply hzK
    have h := hr0 z hzt
    have h1 : ‖z.1‖ ≤ r := (norm_fst_le z).trans h
    rw [Real.norm_eq_abs] at h1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · linarith [neg_abs_le z.1]
    · linarith [le_abs_self z.1]
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_snd_le z).trans h
  have hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume := hr.measurable_velocity
  have hsmall : ∀ a : ℝ, 0 ≤ a → a ≤ 1 + a ^ 2 := fun a _ => by nlinarith [sq_nonneg (a - 1)]
  constructor
  · refine hdom.mono' (hvm.inner hψ.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    by_cases hzK : z ∈ Icc (-r) r ×ˢ Metric.closedBall (0 : Space) r
    · rw [indicator_of_mem hzK, Real.norm_eq_abs]
      have h1 := abs_real_inner_le_norm (v z.1 z.2) (ψ z)
      have h2 := hCψ z
      have h3 := hsmall ‖v z.1 z.2‖ (norm_nonneg _)
      have hC0 : 0 ≤ Cψ := (norm_nonneg _).trans h2
      calc |inner ℝ (v z.1 z.2) (ψ z)| ≤ ‖v z.1 z.2‖ * Cψ :=
            h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
        _ ≤ (1 + ‖v z.1 z.2‖ ^ 2) * Cψ := mul_le_mul_of_nonneg_right h3 hC0
        _ = Cψ * (1 + ‖v z.1 z.2‖ ^ 2) := mul_comm _ _
    · rw [indicator_of_notMem hzK, hz z hzK, inner_zero_right, norm_zero]
  · intro i
    have hcoord : AEStronglyMeasurable (fun z : ℝ × Space => (v z.1 z.2) i) volume :=
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hvm
    refine hdom.mono' (hcoord.mul (hvm.inner hψ.aestronglyMeasurable)) (ae_of_all _ fun z => ?_)
    by_cases hzK : z ∈ Icc (-r) r ×ˢ Metric.closedBall (0 : Space) r
    · rw [indicator_of_mem hzK, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h0 : |(v z.1 z.2) i| ≤ ‖v z.1 z.2‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (v z.1 z.2) i
      have h1 := abs_real_inner_le_norm (v z.1 z.2) (ψ z)
      have h2 := hCψ z
      have hC0 : 0 ≤ Cψ := (norm_nonneg _).trans h2
      calc |(v z.1 z.2) i| * |inner ℝ (v z.1 z.2) (ψ z)| ≤ ‖v z.1 z.2‖ * (‖v z.1 z.2‖ * Cψ) :=
            mul_le_mul h0 (h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))) (abs_nonneg _)
              (norm_nonneg _)
        _ ≤ Cψ * (1 + ‖v z.1 z.2‖ ^ 2) := by nlinarith [norm_nonneg (v z.1 z.2)]
    · rw [indicator_of_notMem hzK, hz z hzK, inner_zero_right, mul_zero, norm_zero]

theorem support_subset_box {ψ : ℝ × Space → Space} (hc : HasCompactSupport ψ) :
    ∃ M : ℕ, ∀ z : ℝ × Space, ψ z ≠ 0 → z ∈ Icc (-(M : ℝ)) M ×ˢ (univ : Set Space) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hc.isCompact.isBounded
  obtain ⟨M, hM⟩ := exists_nat_gt R
  refine ⟨M, fun z hz => ?_⟩
  have h1 : ‖z‖ ≤ R := hR z (subset_tsupport _ hz)
  have h2 : |z.1| ≤ ‖z‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_fst_le z
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · linarith [neg_abs_le z.1]
  · linarith [le_abs_self z.1]

theorem pairing_bound_box {F : ℝ → Space → Space} {ψ : ℝ × Space → Space} {M : ℕ}
    (hM : ∀ z : ℝ × Space, ψ z ≠ 0 → z ∈ Icc (-(M : ℝ)) M ×ˢ (univ : Set Space)) (z : ℝ × Space) :
    ‖inner ℝ (F z.1 z.2) (ψ z)‖ ≤
      (Icc (-(M : ℝ)) M ×ˢ (univ : Set Space)).indicator (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2) z
        + ‖ψ z‖ ^ 2 := by
  by_cases hz : ψ z = 0
  · rw [hz, inner_zero_right, norm_zero]
    exact add_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) _) (sq_nonneg _)
  · rw [indicator_of_mem (hM z hz), Real.norm_eq_abs]
    have h := abs_real_inner_le_norm (F z.1 z.2) (ψ z)
    have h2 : 0 ≤ (‖F z.1 z.2‖ - ‖ψ z‖) ^ 2 := sq_nonneg _
    nlinarith [norm_nonneg (F z.1 z.2), norm_nonneg (ψ z)]

theorem pairing_integrable {F : ℝ → Space → Space} (hF : IsPeriodicField F)
    {ψ : ℝ × Space → Space} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (ψ z)) := by
  obtain ⟨M, hM⟩ := support_subset_box hc
  have hcs : HasCompactSupport (fun z : ℝ × Space => ‖ψ z‖ ^ 2) :=
    hc.comp_left (g := fun x : Space => ‖x‖ ^ 2) (by simp)
  have hcn : Continuous (fun z : ℝ × Space => ‖ψ z‖ ^ 2) := (continuous_norm.comp hψ).pow 2
  have hψ2 : Integrable (fun z : ℝ × Space => ‖ψ z‖ ^ 2) := hcn.integrable_of_hasCompactSupport hcs
  have h1 : Integrable ((Icc (-(M : ℝ)) M ×ˢ (univ : Set Space)).indicator
      (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2)) :=
    (Internal.TestPairing.integrableOn_sq hF M).integrable_indicator
      (measurableSet_Icc.prod MeasurableSet.univ)
  have h3 : Integrable (fun z : ℝ × Space =>
      (Icc (-(M : ℝ)) M ×ˢ (univ : Set Space)).indicator (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2) z
        + ‖ψ z‖ ^ 2) := h1.add hψ2
  have h4 : AEStronglyMeasurable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (ψ z)) volume :=
    hF.1.inner hψ.aestronglyMeasurable
  exact h3.mono' h4 (ae_of_all _ fun z => pairing_bound_box hM z)

theorem actuator_periodic {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (i : Fin k) :
    IsPeriodicField (d.actuator i) := by
  refine ⟨hd.actuator_measurable i, hd.actuator_periodic i, lt_of_le_of_lt ?_
    (lt_of_le_of_lt hd.actuator_norm ENNReal.ofReal_lt_top)⟩
  exact Finset.single_le_sum (f := fun j => periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2))
    (fun j _ => bot_le) (Finset.mem_univ i)

theorem actuator_integrable {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    (m : Fin k → ℝ) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (∑ i, m i • d.actuator i z.1 z.2) (φ z.1 z.2)) := by
  have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  have he : (fun z : ℝ × Space => inner ℝ (∑ i, m i • d.actuator i z.1 z.2) (φ z.1 z.2)) =
      fun z => ∑ i, m i * inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2) := by
    funext z
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  rw [he]
  exact integrable_finsetSum _ fun i _ =>
    (pairing_integrable (actuator_periodic hd i) hφc hφ.2.1).const_mul (m i)

theorem column_periodic {Γ : Set Symmetry} {P : ℝ} {v : VelField} {G : GradField}
    {H : SecondField} {g : ℝ → Space → Space} (hg : IsPerturbation Γ P v G H g) (i : Fin 3) :
    IsPeriodicField (fun σ y => G σ y (unitVector i)) := by
  refine ⟨(ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
    hg.measurable_gradient, fun σ y => by simp only [hg.periodic_gradient σ y],
    lt_of_le_of_lt ?_ hg.gradient_finite⟩
  refine setLIntegral_mono' measurableSet_Icc fun σ _ => lintegral_mono fun y => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  exact Finset.single_le_sum (f := fun j : Fin 3 => ‖G σ y (unitVector j)‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem lin_integrable {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) {Γ : Set Symmetry} {P : ℝ}
    {g : ℝ → Space → Space} (hg : IsPerturbation Γ P v G H g) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (transportTest P φ z)) ∧
    Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) ∧
    Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)) := by
  have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  obtain ⟨hD, hDc⟩ := test_fderiv hφ
  obtain ⟨hT, hTc⟩ := test_deriv hφ
  have hDy : Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 z.2) := hD.clm_apply continuous_snd
  have hDyc : HasCompactSupport (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 z.2) :=
    hDc.mono fun z hz h0 => hz (show fderiv ℝ (φ z.1) z.2 z.2 = 0 by
      rw [show fderiv ℝ (φ z.1) z.2 = 0 from h0]; rfl)
  refine ⟨(velocity_local hr hsup (ψ := transportTest P φ)
      (((hT.const_smul (-(1 / P))).sub hφc).sub (hDy.const_smul (1 / 2 : ℝ)))
      (((hTc.smul_left (f := fun _ => -(1 / P))).sub hφ.2.1).sub
        (hDyc.smul_left (f := fun _ => (1 / 2 : ℝ))))).1, ?_,
    pairing_integrable ⟨hg.measurable_derivative, hg.periodic_derivative, hg.derivative_finite⟩
      hφc hφ.2.1⟩
  exact integrable_finsetSum _ fun i _ => pairing_integrable (column_periodic hg i)
    (hD.clm_apply continuous_const)
    (hDc.mono fun z hz h0 => hz (show fderiv ℝ (φ z.1) z.2 (unitVector i) = 0 by
      rw [show fderiv ℝ (φ z.1) z.2 = 0 from h0]; rfl))

theorem bar_inr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × Space → E}
    (hF : Differentiable ℝ F) (z : ℝ × Space) (w : Space) :
    fderiv ℝ (fun y => F (z.1, y)) z.2 w = fderiv ℝ F z (0, w) := by
  have h : HasFDerivAt (fun y => F (z.1, y))
      ((fderiv ℝ F (z.1, z.2)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) z.2 :=
    (hF (z.1, z.2)).hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)
  rw [h.fderiv]
  rfl

theorem bar_inl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × Space → E}
    (hF : Differentiable ℝ F) (z : ℝ × Space) :
    deriv (fun s => F (s, z.2)) z.1 = fderiv ℝ F z (1, 0) := by
  have h : HasDerivAt (fun s => F (s, z.2)) (fderiv ℝ F (z.1, z.2) (1, 0)) z.1 :=
    (hF (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  exact h.deriv

theorem bar_cst_inner_right {a b : ℝ × Space → Space} (hb : HasCompactSupport b) :
    HasCompactSupport (fun z => inner ℝ (a z) (b z)) := by
  refine hb.mono fun z hz => ?_
  simp only [Function.mem_support, ne_eq] at hz ⊢
  intro h
  apply hz
  rw [h, inner_zero_right]

def barFlux (f f' g' : ℝ × Space → Space) (φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  inner ℝ (f z) (g' z) + inner ℝ (f' z) (φ z.1 z.2)

theorem bar_parts_zero {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ)
    {f f' g' : ℝ × Space → Space} (w : ℝ × Space) (hf : ContDiff ℝ 1 f)
    (hf' : ∀ z, fderiv ℝ f z w = f' z)
    (hg' : ∀ z, fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z w = g' z) :
    Integrable (barFlux f f' g' φ) ∧ ∫ z, barFlux f f' g' φ z = 0 := by
  obtain rfl : f' = fun z => fderiv ℝ f z w := funext fun z => (hf' z).symm
  obtain rfl : g' = fun z => fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z w :=
    funext fun z => (hg' z).symm
  have hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2) := hφ.1
  have hc : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2) := hφ.2.1
  have hfd : Continuous (fun z => fderiv ℝ f z w) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgd : Continuous (fun z => fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z w) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgdc : HasCompactSupport (fun z => fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z w) :=
    hc.fderiv_apply (𝕜 := ℝ) w
  have i1 : Integrable (fun z => inner ℝ (fderiv ℝ f z w) (φ z.1 z.2)) :=
    (hfd.inner hs.continuous).integrable_of_hasCompactSupport (bar_cst_inner_right hc)
  have i2 : Integrable (fun z => inner ℝ (f z) (fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z w)) :=
    (hf.continuous.inner hgd).integrable_of_hasCompactSupport (bar_cst_inner_right hgdc)
  have i3 : Integrable (fun z => inner ℝ (f z) (φ z.1 z.2)) :=
    (hf.continuous.inner hs.continuous).integrable_of_hasCompactSupport (bar_cst_inner_right hc)
  have : (volume : Measure (ℝ × Space)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have key : ∫ z, inner ℝ (f z) (fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z w) =
      -∫ z, inner ℝ (fderiv ℝ f z w) (φ z.1 z.2) :=
    integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := innerSL ℝ) (f := f) (g := fun z : ℝ × Space => φ z.1 z.2) (v := w) i1 i2 i3
    (fun x _ => (hf.differentiable one_ne_zero) x) (fun x _ => (hs.differentiable (by simp)) x)
  refine ⟨i2.add i1, ?_⟩
  unfold barFlux
  rw [integral_add i2 i1, key, neg_add_cancel]

theorem bar_deriv_Y {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (z : ℝ × Space) (i : Fin 3) :
    fderiv ℝ (fun z : ℝ × Space => z.2 i • W z.1 z.2) z (0, unitVector i) =
      W z.1 z.2 + z.2 i • fderiv ℝ (W z.1) z.2 (unitVector i) := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable (by norm_num)
  have hp : HasFDerivAt (fun z : ℝ × Space => z.2 i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space)) z :=
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt
  have h1 : (unitVector i) i = 1 := by simp [unitVector]
  rw [(show HasFDerivAt (fun z : ℝ × Space => z.2 i • W z.1 z.2) _ z from
    hp.smul (hWd z).hasFDerivAt).fderiv, bar_inr hWd z]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', PiLp.proj_apply, h1, one_smul]
  abel

theorem bar_deriv_A {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (z : ℝ × Space) (i : Fin 3) :
    fderiv ℝ (fun z : ℝ × Space => (W z.1 z.2) i • W z.1 z.2) z (0, unitVector i) =
      (fderiv ℝ (W z.1) z.2 (unitVector i)) i • W z.1 z.2
        + (W z.1 z.2) i • fderiv ℝ (W z.1) z.2 (unitVector i) := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable (by norm_num)
  have hp : HasFDerivAt (fun z : ℝ × Space => (W z.1 z.2) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z)) z :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp z (hWd z).hasFDerivAt
  rw [(show HasFDerivAt (fun z : ℝ × Space => (W z.1 z.2) i • W z.1 z.2) _ z from
    hp.smul (hWd z).hasFDerivAt).fderiv, bar_inr hWd z]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  abel

theorem bar_slice_contDiff {W : ℝ → Space → Space} {n : ℕ∞}
    (hW : ContDiff ℝ n (fun z : ℝ × Space => W z.1 z.2)) (σ : ℝ) : ContDiff ℝ n (W σ) :=
  hW.comp (contDiff_const.prodMk contDiff_id)

theorem bar_L_eq {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (i : Fin 3) : (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector i)) =
      fun z => fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (0, unitVector i) :=
  funext fun z => bar_inr (hW.differentiable (by norm_num)) z (unitVector i)

theorem bar_L_contDiff {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (i : Fin 3) : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector i)) := by
  rw [bar_L_eq hW i]
  exact (hW.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem bar_deriv_L {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (z : ℝ × Space) (i : Fin 3) :
    fderiv ℝ (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector i)) z (0, unitVector i) =
      iteratedFDeriv ℝ 2 (W z.1) z.2 ![unitVector i, unitVector i] := by
  have hd := (bar_L_contDiff hW i).differentiable one_ne_zero
  rw [← bar_inr hd z]
  have hs : ContDiff ℝ 2 (W z.1) := bar_slice_contDiff hW z.1
  have hc : DifferentiableAt ℝ (fderiv ℝ (W z.1)) z.2 :=
    (hs.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z.2
  rw [fderiv_clm_apply hc (differentiableAt_const _), iteratedFDeriv_two_apply]
  simp

theorem bar_deriv_Q {q : ℝ → Space → ℝ} (hq : ContDiff ℝ 1 (fun z : ℝ × Space => q z.1 z.2))
    (z : ℝ × Space) (i : Fin 3) :
    fderiv ℝ (fun z : ℝ × Space => q z.1 z.2 • unitVector i) z (0, unitVector i) =
      fderiv ℝ (q z.1) z.2 (unitVector i) • unitVector i := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => q z.1 z.2) := hq.differentiable one_ne_zero
  rw [fderiv_smul_const (hd z), ContinuousLinearMap.smulRight_apply, bar_inr hd z]

theorem bar_inner_unit (i : Fin 3) (x : Space) : inner ℝ (unitVector i) x = x i := by
  simp [unitVector, EuclideanSpace.inner_single_left]

def barT (W φ : ℝ → Space → Space) : ℝ × Space → ℝ :=
  barFlux (fun z => W z.1 z.2) (fun z => deriv (fun s => W s z.2) z.1)
    (fun z => deriv (fun s => φ s z.2) z.1) φ

def barY (W φ : ℝ → Space → Space) (i : Fin 3) : ℝ × Space → ℝ :=
  barFlux (fun z => z.2 i • W z.1 z.2)
    (fun z => W z.1 z.2 + z.2 i • fderiv ℝ (W z.1) z.2 (unitVector i))
    (fun z => fderiv ℝ (φ z.1) z.2 (unitVector i)) φ

def barL (W φ : ℝ → Space → Space) (i : Fin 3) : ℝ × Space → ℝ :=
  barFlux (fun z => fderiv ℝ (W z.1) z.2 (unitVector i))
    (fun z => iteratedFDeriv ℝ 2 (W z.1) z.2 ![unitVector i, unitVector i])
    (fun z => fderiv ℝ (φ z.1) z.2 (unitVector i)) φ

def barA (W φ : ℝ → Space → Space) (i : Fin 3) : ℝ × Space → ℝ :=
  barFlux (fun z => (W z.1 z.2) i • W z.1 z.2)
    (fun z => (fderiv ℝ (W z.1) z.2 (unitVector i)) i • W z.1 z.2
      + (W z.1 z.2) i • fderiv ℝ (W z.1) z.2 (unitVector i))
    (fun z => fderiv ℝ (φ z.1) z.2 (unitVector i)) φ

def barQ (q : ℝ → Space → ℝ) (φ : ℝ → Space → Space) (i : Fin 3) : ℝ × Space → ℝ :=
  barFlux (fun z => q z.1 z.2 • unitVector i)
    (fun z => fderiv ℝ (q z.1) z.2 (unitVector i) • unitVector i)
    (fun z => fderiv ℝ (φ z.1) z.2 (unitVector i)) φ

def barE (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (φ : ℝ → Space → Space) (i : Fin 3)
    (z : ℝ × Space) : ℝ :=
  -(1 / 2 : ℝ) * barY W φ i z + barL W φ i z - barA W φ i z - barQ q φ i z

theorem bar_pointwise {k : ℕ} (P : ℝ) {W : ℝ → Space → Space} (q : ℝ → Space → ℝ)
    (b : Fin k → ℝ → Space → Space) {φ : ℝ → Space → Space}
    (hdivW : ∀ σ y, divergenceAt (W σ) y = 0) (hdivφ : ∀ s y, divergenceAt (φ s) y = 0)
    (z : ℝ × Space) :
    barPart P W φ z = inner ℝ (defectField P W q b 0 z.1 z.2) (φ z.1 z.2)
      + (-(1 / P) * barT W φ z + ∑ i : Fin 3, barE W q φ i z) := by
  have h1 := hdivW z.1 z.2
  have h2 := hdivφ z.1 z.2
  simp only [divergenceAt, Fin.sum_univ_three] at h1 h2
  simp only [barPart, sigmaSimilarityIntegrand, defectField, barT, barE, barY, barL, barA, barQ, barFlux,
    sumSecondPartialsAt, advectionAt, gradientAt, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
    add_zero]
  rw [Internal.Convection.apply_eq_sum_unitVector (fderiv ℝ (φ z.1) z.2) z.2,
    Internal.Convection.apply_eq_sum_unitVector (fderiv ℝ (W z.1) z.2) z.2,
    Internal.Convection.apply_eq_sum_unitVector (fderiv ℝ (W z.1) z.2) (W z.1 z.2)]
  simp only [Fin.sum_univ_three, inner_add_left, inner_add_right, inner_sub_left,
    real_inner_smul_left, real_inner_smul_right, bar_inner_unit]
  linear_combination (inner ℝ (W z.1 z.2) (φ z.1 z.2)) * h1 + q z.1 z.2 * h2

theorem bar_T_zero {W φ : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hφ : IsSpaceTimeTestField φ) :
    Integrable (barT W φ) ∧ ∫ z, barT W φ z = 0 := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable (by norm_num)
  have hΦd : Differentiable ℝ (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.differentiable (by simp)
  exact bar_parts_zero hφ (1, 0) (hW.of_le (by norm_num)) (fun z => (bar_inl hWd z).symm)
    (fun z => (bar_inl hΦd z).symm)

theorem bar_E_zero {W φ : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hq : ContDiff ℝ 1 (fun z : ℝ × Space => q z.1 z.2)) (hφ : IsSpaceTimeTestField φ)
    (i : Fin 3) : Integrable (barE W q φ i) ∧ ∫ z, barE W q φ i z = 0 := by
  have hΦd : Differentiable ℝ (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.differentiable (by simp)
  have gφ : ∀ z : ℝ × Space, fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (0, unitVector i) =
      fderiv ℝ (φ z.1) z.2 (unitVector i) := fun z => (bar_inr hΦd z _).symm
  have hW1 : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2) := hW.of_le (by norm_num)
  have hpr : ContDiff ℝ 1 (fun z : ℝ × Space => z.2 i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have hpW : ContDiff ℝ 1 (fun z : ℝ × Space => (W z.1 z.2) i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hW1
  obtain ⟨iY, eY⟩ : Integrable (barY W φ i) volume ∧ ∫ z, barY W φ i z = 0 :=
    bar_parts_zero hφ (0, unitVector i) (f := fun z => z.2 i • W z.1 z.2) (hpr.smul hW1) (fun z => bar_deriv_Y hW z i) gφ
  obtain ⟨iL, eL⟩ : Integrable (barL W φ i) volume ∧ ∫ z, barL W φ i z = 0 :=
    bar_parts_zero hφ (0, unitVector i) (bar_L_contDiff hW i) (fun z => bar_deriv_L hW z i) gφ
  obtain ⟨iA, eA⟩ : Integrable (barA W φ i) volume ∧ ∫ z, barA W φ i z = 0 :=
    bar_parts_zero hφ (0, unitVector i) (f := fun z => (W z.1 z.2) i • W z.1 z.2) (hpW.smul hW1) (fun z => bar_deriv_A hW z i) gφ
  obtain ⟨iQ, eQ⟩ : Integrable (barQ q φ i) volume ∧ ∫ z, barQ q φ i z = 0 :=
    bar_parts_zero hφ (0, unitVector i) (f := fun z => q z.1 z.2 • unitVector i) (hq.smul contDiff_const) (fun z => bar_deriv_Q hq z i) gφ
  have j1 : Integrable (fun z => -(1 / 2 : ℝ) * barY W φ i z) := iY.const_mul _
  have j2 : Integrable (fun z => -(1 / 2 : ℝ) * barY W φ i z + barL W φ i z) := j1.add iL
  have j3 : Integrable (fun z => -(1 / 2 : ℝ) * barY W φ i z + barL W φ i z - barA W φ i z) :=
    j2.sub iA
  refine ⟨j3.sub iQ, ?_⟩
  show ∫ z, (-(1 / 2 : ℝ) * barY W φ i z + barL W φ i z - barA W φ i z - barQ q φ i z) = 0
  rw [integral_sub j3 iQ, integral_sub j2 iA, integral_add j1 iL, integral_const_mul, eY, eL, eA, eQ]
  ring

theorem bar_S_eq {k : ℕ} (P : ℝ) {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (b : Fin k → ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hq : ContDiff ℝ 1 (fun z : ℝ × Space => q z.1 z.2)) (z : ℝ × Space) :
    defectField P W q b 0 z.1 z.2 =
      (1 / P) • fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (1, 0)
        + (1 / 2 : ℝ) • W z.1 z.2
        + (1 / 2 : ℝ) • fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (0, z.2)
        - ∑ i : Fin 3, fderiv ℝ (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector i)) z
            (0, unitVector i)
        + fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (0, W z.1 z.2)
        + ∑ i : Fin 3, fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) z (0, unitVector i) • unitVector i := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable (by norm_num)
  have hqd : Differentiable ℝ (fun z : ℝ × Space => q z.1 z.2) := hq.differentiable one_ne_zero
  have eW : ∀ w, fderiv ℝ (W z.1) z.2 w = fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (0, w) :=
    fun w => bar_inr hWd z w
  have eq : ∀ w, fderiv ℝ (q z.1) z.2 w = fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) z (0, w) :=
    fun w => bar_inr hqd z w
  have et : deriv (fun s => W s z.2) z.1 = fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (1, 0) :=
    bar_inl hWd z
  simp only [defectField, sumSecondPartialsAt, advectionAt, gradientAt, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero, ← bar_deriv_L hW z]
  rw [et, eW z.2, eW (W z.1 z.2)]
  simp only [eq]

theorem bar_S_continuous {k : ℕ} (P : ℝ) {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (b : Fin k → ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hq : ContDiff ℝ 1 (fun z : ℝ × Space => q z.1 z.2)) :
    Continuous (fun z : ℝ × Space => defectField P W q b 0 z.1 z.2) := by
  rw [funext (bar_S_eq P b hW hq)]
  have hWc : Continuous (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z) :=
    hW.continuous_fderiv (by norm_num)
  have hqc : Continuous (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) z) :=
    hq.continuous_fderiv one_ne_zero
  have hL : ∀ i : Fin 3, Continuous (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector i)) z (0, unitVector i)) :=
    fun i => ((bar_L_contDiff hW i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h0 : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  refine Continuous.add (Continuous.add (Continuous.sub (Continuous.add (Continuous.add ?_ ?_) ?_) ?_) ?_) ?_
  · exact (hWc.clm_apply continuous_const).const_smul (1 / P)
  · exact h0.const_smul (1 / 2 : ℝ)
  · exact (hWc.clm_apply (continuous_const.prodMk continuous_snd)).const_smul (1 / 2 : ℝ)
  · exact continuous_finsetSum _ fun i _ => hL i
  · exact hWc.clm_apply (continuous_const.prodMk h0)
  · exact continuous_finsetSum _ fun i _ => (hqc.clm_apply continuous_const).smul continuous_const

theorem bar_identity_general {k : ℕ} (P : ℝ) {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (b : Fin k → ℝ → Space → Space) {φ : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hq : ContDiff ℝ 1 (fun z : ℝ × Space => q z.1 z.2))
    (hdivW : ∀ σ y, divergenceAt (W σ) y = 0) (hφ : IsSpaceTimeTestField φ) :
    Integrable (barPart P W φ) ∧
    Integrable (fun z : ℝ × Space => inner ℝ (defectField P W q b 0 z.1 z.2) (φ z.1 z.2)) ∧
    ∫ z, barPart P W φ z = ∫ z : ℝ × Space, inner ℝ (defectField P W q b 0 z.1 z.2) (φ z.1 z.2) := by
  have iS : Integrable (fun z : ℝ × Space => inner ℝ (defectField P W q b 0 z.1 z.2) (φ z.1 z.2)) :=
    ((bar_S_continuous P b hW hq).inner hφ.1.continuous).integrable_of_hasCompactSupport
      (bar_cst_inner_right hφ.2.1)
  obtain ⟨iT, eT⟩ := bar_T_zero hW hφ
  have iE : Integrable (fun z => ∑ i : Fin 3, barE W q φ i z) :=
    integrable_finsetSum _ fun i _ => (bar_E_zero hW hq hφ i).1
  have eE : ∫ z, ∑ i : Fin 3, barE W q φ i z = 0 := by
    rw [integral_finsetSum _ fun i _ => (bar_E_zero hW hq hφ i).1]
    exact Finset.sum_eq_zero fun i _ => (bar_E_zero hW hq hφ i).2
  have iT' : Integrable (fun z => -(1 / P) * barT W φ z) := iT.const_mul _
  have iR : Integrable (fun z => -(1 / P) * barT W φ z + ∑ i : Fin 3, barE W q φ i z) := iT'.add iE
  have eR : ∫ z, (-(1 / P) * barT W φ z + ∑ i : Fin 3, barE W q φ i z) = 0 := by
    rw [integral_add iT' iE, integral_const_mul, eT, eE]
    ring
  have hpt := bar_pointwise P q b hdivW hφ.2.2
  have hfun : barPart P W φ = fun z => inner ℝ (defectField P W q b 0 z.1 z.2) (φ z.1 z.2)
      + (-(1 / P) * barT W φ z + ∑ i : Fin 3, barE W q φ i z) := funext hpt
  refine ⟨hfun ▸ iS.add iR, iS, ?_⟩
  rw [hfun, integral_add iS iR, eR, add_zero]

theorem bar_identity {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (barPart (d.period p) (d.profile p) φ) ∧
    Integrable (fun z : ℝ × Space => inner ℝ
      (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator 0 z.1 z.2) (φ z.1 z.2)) ∧
    ∫ z, barPart (d.period p) (d.profile p) φ z = ∫ z : ℝ × Space, inner ℝ
      (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator 0 z.1 z.2) (φ z.1 z.2) :=
  bar_identity_general (d.period p) d.actuator
    (Internal.Convection.isCoefficient_profile hd hp).smooth (hd.pressure_smooth p hp)
    (hd.profile_divergence p hp) hφ

open Internal.Convection

theorem cross_inner_unit (x : Space) (i : Fin 3) : inner ℝ x (unitVector i) = x i := by
  simp [unitVector, EuclideanSpace.inner_single_right]

def crossTest (W φ : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  ∑ i : Fin 3, ((W z.1 z.2) i • fderiv ℝ (φ z.1) z.2 (unitVector i)
    + inner ℝ (W z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i)) • unitVector i)

theorem cross_eq_inner (W v φ : ℝ → Space → Space) (z : ℝ × Space) :
    crossPart W v φ z = -inner ℝ (v z.1 z.2) (crossTest W φ z) := by
  simp only [crossPart, crossTest, inner_add_right, inner_smul_right, cross_inner_unit,
    Fin.sum_univ_three]
  ring

theorem cross_integrable {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) : Integrable (crossPart (d.profile p) v φ) := by
  have hW := (isCoefficient_profile hd hp).smooth.continuous
  obtain ⟨hc, hs⟩ := test_fderiv hφ
  have hcont : Continuous (crossTest (d.profile p) φ) := by
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector i)) :=
      hc.clm_apply continuous_const
    have h2 : Continuous (fun z : ℝ × Space =>
        inner ℝ (d.profile p z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i))) := hW.inner h1
    exact ((((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hW)).smul h1).add
      (h2.smul continuous_const)
  have hsupp : HasCompactSupport (crossTest (d.profile p) φ) := by
    refine hs.mono fun z hz => ?_
    intro h0
    apply hz
    simp only [crossTest, h0, zero_apply, smul_zero, inner_zero_right,
      zero_smul, add_zero, Finset.sum_const_zero]
  have h := (velocity_local hr hsup hcont hsupp).1.neg
  refine h.congr (ae_of_all _ fun z => ?_)
  exact (cross_eq_inner _ _ _ z).symm

theorem cross_conv_integrable {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.box) {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ
      (G z.1 z.2 (d.profile p z.1 z.2) + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) := by
  have hW := isCoefficient_profile hd hp
  have hs := readingConvection_slice hr (d.profile p)
  have hF : IsPeriodicField (readingConvection (d.profile p) v G) :=
    ⟨aesm_readingConvection hW hr.measurable_velocity hr.measurable_gradient,
      periodic_readingConvection hW hr,
      lt_of_le_of_lt (periodLIntegral_le hW u _ hs) ENNReal.ofReal_lt_top⟩
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hφ.2.1
  have h : Integrable (fun z : ℝ × Space => inner ℝ (readingConvection (d.profile p) v G z.1 z.2)
      (φ z.1 z.2)) := Internal.TestPairing.integrable_pairing hF hφ.1 hφ.2.1 hR
  simpa only [readingConvection] using h


open WeakProfile.Internal.AdvectionByParts in
theorem cross_pair_expand (a b : Space → Space) (ψ : Space → Space) (y : Space) :
    pairForm ψ (a + b) (a + b) y =
      pairForm ψ a a y + pairForm ψ a b y + pairForm ψ b a y + pairForm ψ b b y := by
  simp only [pairForm, Pi.add_apply, PiLp.add_apply, inner_add_left, Fin.sum_univ_three]
  ring

theorem cross_tri_expand (a b : Space → Space) (c d : Fin 3 → Space → Space) (ψ : Space → Space)
    (y : Space) :
    ∑ j : Fin 3, (a + b) y j * inner ℝ ((c j + d j) y) (ψ y) =
      ∑ j : Fin 3, a y j * inner ℝ (c j y) (ψ y) + ∑ j : Fin 3, a y j * inner ℝ (d j y) (ψ y)
      + ∑ j : Fin 3, b y j * inner ℝ (c j y) (ψ y) + ∑ j : Fin 3, b y j * inner ℝ (d j y) (ψ y) := by
  simp only [Pi.add_apply, PiLp.add_apply, inner_add_left, Fin.sum_univ_three]
  ring

def crossTri (a : Space → Space) (c : Fin 3 → Space → Space) (ψ : Space → Space) (y : Space) : ℝ :=
  ∑ j : Fin 3, a y j * inner ℝ (c j y) (ψ y)

open WeakProfile.Internal.AdvectionByParts in
theorem cross_polarize_gen {ψ : Space → Space} (a b s : Space → Space) (ca cb cs : Fin 3 → Space → Space)
    (hs : s =ᵐ[volume] a + b) (hc : ∀ᵐ y, ∀ j, cs j y = ca j y + cb j y)
    (i1 : Integrable (pairForm ψ a a)) (i2 : Integrable (pairForm ψ a b))
    (i3 : Integrable (pairForm ψ b a)) (i4 : Integrable (pairForm ψ b b))
    (j1 : Integrable (crossTri a ca ψ)) (j2 : Integrable (crossTri a cb ψ))
    (j3 : Integrable (crossTri b ca ψ)) (j4 : Integrable (crossTri b cb ψ))
    (e0 : ∫ y, pairForm ψ s s y = -∫ y, crossTri s cs ψ y)
    (e1 : ∫ y, pairForm ψ a a y = -∫ y, crossTri a ca ψ y)
    (e2 : ∫ y, pairForm ψ b b y = -∫ y, crossTri b cb ψ y) :
    (∫ y, pairForm ψ a b y) + ∫ y, pairForm ψ b a y =
      -((∫ y, crossTri a cb ψ y) + ∫ y, crossTri b ca ψ y) := by
  have eL : ∫ y, pairForm ψ s s y = (∫ y, pairForm ψ a a y) + (∫ y, pairForm ψ a b y)
      + (∫ y, pairForm ψ b a y) + ∫ y, pairForm ψ b b y := by
    have i12 : Integrable (fun y => pairForm ψ a a y + pairForm ψ a b y) := i1.add i2
    have i123 : Integrable (fun y => pairForm ψ a a y + pairForm ψ a b y + pairForm ψ b a y) :=
      i12.add i3
    rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4]
    refine integral_congr_ae ?_
    filter_upwards [hs] with y hy
    unfold pairForm
    rw [hy]
    simp only [Pi.add_apply, PiLp.add_apply, inner_add_left, Fin.sum_univ_three]
    ring
  have eR : ∫ y, crossTri s cs ψ y = (∫ y, crossTri a ca ψ y) + (∫ y, crossTri a cb ψ y)
      + (∫ y, crossTri b ca ψ y) + ∫ y, crossTri b cb ψ y := by
    have j12 : Integrable (fun y => crossTri a ca ψ y + crossTri a cb ψ y) := j1.add j2
    have j123 : Integrable (fun y => crossTri a ca ψ y + crossTri a cb ψ y + crossTri b ca ψ y) :=
      j12.add j3
    rw [← integral_add j1 j2, ← integral_add j12 j3, ← integral_add j123 j4]
    refine integral_congr_ae ?_
    filter_upwards [hs, hc] with y hy hj
    unfold crossTri
    rw [hy]
    simp only [hj, Pi.add_apply, PiLp.add_apply, inner_add_left, Fin.sum_univ_three]
    ring
  rw [eL, eR] at e0
  linarith

open WeakProfile.Internal.AdvectionByParts in
theorem cross_polarize (w x : X) {ψ : Space → Space} (hψ : IsTestField ψ) :
    (∫ y, pairForm ψ (velocity w) (velocity x) y) + ∫ y, pairForm ψ (velocity x) (velocity w) y =
      -(trilinear w x ψ + trilinear x w ψ) := by
  obtain ⟨K, hK⟩ := pairForm_bound hψ
  have hψ2 : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hψ6 : MemLp ψ 6 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  obtain ⟨C, hC⟩ := trilinear_holds
  have hv : (velocity (w + x) : Space → Space) =ᵐ[volume]
      (velocity w : Space → Space) + (velocity x : Space → Space) := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hpj : ∀ᵐ y, ∀ j : Fin 3, (partialX j (w + x) : Space → Space) y =
      (partialX j w : Space → Space) y + (partialX j x : Space → Space) y := by
    refine ae_all_iff.2 fun j => ?_
    have h := Lp.coeFn_add (partialX j w) (partialX j x)
    rw [← map_add] at h
    filter_upwards [h] with y hy
    rw [hy, Pi.add_apply]
  have key := cross_polarize_gen (ψ := ψ) _ _ _ (fun j => (partialX j w : Space → Space))
    (fun j => (partialX j x : Space → Space)) (fun j => (partialX j (w + x) : Space → Space)) hv hpj
    (hK _ _).1 (hK _ _).1 (hK _ _).1 (hK _ _).1
    (hC w w ψ hψ2 hψ6).1 (hC w x ψ hψ2 hψ6).1 (hC x w ψ hψ2 hψ6).1 (hC x x ψ hψ2 hψ6).1
    (WeakProfile.advectionByParts_holds (w + x) ψ hψ) (WeakProfile.advectionByParts_holds w ψ hψ)
    (WeakProfile.advectionByParts_holds x ψ hψ)
  exact key

theorem cross_isSlice {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) (σ : ℝ) : ∃ C, WeakProfile.IsSlice (d.profile p σ)
      (fun y => fderiv ℝ (d.profile p σ) y) C := by
  have hW := isCoefficient_profile hd hp
  have hs : ContDiff ℝ 2 (d.profile p σ) := Internal.Convection.slice_contDiff hW σ
  have hc : Continuous (d.profile p σ) := hs.continuous
  have hdc : Continuous (fun y => fderiv ℝ (d.profile p σ) y) := hs.continuous_fderiv (by norm_num)
  have hdiff : Differentiable ℝ (d.profile p σ) := hs.differentiable (by norm_num)
  have hfin6 : (Module.finrank ℝ Space : ℝ) < 6 := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]; norm_num
  have hfin4 : (Module.finrank ℝ Space : ℝ) < 4 := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]; norm_num
  have i6 : Integrable (fun y : Space => d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ))) :=
    (integrable_one_add_norm hfin6).const_mul _
  have i4 : Integrable (fun y : Space => d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm hfin4).const_mul _
  have b6 : ∀ y, ‖d.profile p σ y‖ ^ 6 ≤ d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)) := by
    intro y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    calc ‖d.profile p σ y‖ ^ 6 ≤ (d.decay / (1 + ‖y‖)) ^ 6 :=
          pow_le_pow_left₀ (norm_nonneg _) (hW.bound_zero σ y) 6
      _ = d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)) := by
          rw [div_pow, Real.rpow_neg hpos.le, div_eq_mul_inv]
          norm_cast
  have b2 : ∀ y, ‖fderiv ℝ (d.profile p σ) y‖ ^ 2 ≤ d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
    intro y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    calc ‖fderiv ℝ (d.profile p σ) y‖ ^ 2 ≤ (d.decay / (1 + ‖y‖) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hW.bound_one σ y) 2
      _ = d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
          rw [div_pow, ← pow_mul, Real.rpow_neg hpos.le, div_eq_mul_inv]
          norm_num
  have n6 : 0 ≤ ∫ y : Space, d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)) :=
    integral_nonneg fun y => by positivity
  have n4 : 0 ≤ ∫ y : Space, d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) :=
    integral_nonneg fun y => by positivity
  refine ⟨(∫ y : Space, d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)))
    + ∫ y : Space, d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)), ⟨⟨hc.locallyIntegrable, hdc.locallyIntegrable,
      fun ψ hψ i => ?_⟩, ae_of_all _ fun y => hd.profile_divergence p hp σ y, ?_, ?_⟩⟩
  · have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
    have hψc : Continuous (fun y => fderiv ℝ ψ y (unitVector i)) :=
      (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have h1 : Integrable (fun y => fderiv ℝ ψ y (unitVector i) • d.profile p σ y) :=
      (hψc.smul hc).integrable_of_hasCompactSupport
        ((hψ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)).smul_right)
    have h2 : Integrable (fun y => ψ y • fderiv ℝ (d.profile p σ) y (unitVector i)) :=
      (hψ.1.continuous.smul (hdc.clm_apply continuous_const)).integrable_of_hasCompactSupport
        hψ.2.smul_right
    have h3 : Integrable (fun y => ψ y • d.profile p σ y) :=
      (hψ.1.continuous.smul hc).integrable_of_hasCompactSupport hψ.2.smul_right
    exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h3 (fun y _ => hψd y)
      (fun y _ => hdiff y)
  · refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right n4))
    rw [ofReal_integral_eq_lintegral_ofReal i6 (ae_of_all _ fun y => by positivity)]
    exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal (b6 y)
  · refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left n6))
    rw [ofReal_integral_eq_lintegral_ofReal i4 (ae_of_all _ fun y => by positivity)]
    exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal (b2 y)

theorem cross_profile_embed {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.box) (σ : ℝ) :
    ∃ w : X, (velocity w : Space → Space) =ᵐ[volume] d.profile p σ ∧
      ∀ j : Fin 3, (partialX j w : Space → Space) =ᵐ[volume]
        fun y => fderiv ℝ (d.profile p σ) y (unitVector j) := by
  obtain ⟨C, hC⟩ := cross_isSlice hd hp σ
  obtain ⟨w, h1, h2, -⟩ := WeakProfile.sliceEmbedding_holds WeakProfile.pairingVelocity_holds
    WeakProfile.velocityWeakGradient_holds WeakProfile.zeroGradientSix_holds
    WeakProfile.gradientFreqTr_holds _ _ C hC
  exact ⟨w, h1, h2⟩

open WeakProfile.Internal.AdvectionByParts in
theorem cross_slice_left (W v φ : ℝ → Space → Space) (σ : ℝ) (a b : Space → Space) (y : Space)
    (h1 : v σ y = b y) (h2 : a y = W σ y) :
    crossPart W v φ (σ, y) = -(pairForm (φ σ) a b y + pairForm (φ σ) b a y) := by
  simp only [crossPart, pairForm]
  rw [h1, ← h2]
  ring

theorem cross_slice_right (Gy DW : Space →L[ℝ] Space) (Wy vy ψy : Space) (a b : Space → Space)
    (ca cb : Fin 3 → Space → Space) (y : Space) (h1 : vy = b y) (h2 : a y = Wy)
    (h3 : ∀ j, Gy (unitVector j) = cb j y) (h4 : ∀ j, ca j y = DW (unitVector j)) :
    inner ℝ (Gy Wy + DW vy) ψy =
      ∑ j : Fin 3, a y j * inner ℝ (cb j y) ψy + ∑ j : Fin 3, b y j * inner ℝ (ca j y) ψy := by
  rw [inner_add_left, ← Breakdown.Freq.Internal.Advection.sum_coord_inner Gy,
    ← Breakdown.Freq.Internal.Advection.sum_coord_inner DW]
  simp only [h3, ← h4, h1, ← h2]

theorem cross_slice {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ∀ᵐ σ : ℝ, ∫ y, crossPart (d.profile p) v φ (σ, y) = ∫ y, inner ℝ
      (G σ y (d.profile p σ y) + fderiv ℝ (d.profile p σ) y (v σ y)) (φ σ y) := by
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hφ.2.1
  obtain ⟨C, hC⟩ := trilinear_holds
  filter_upwards [hr.velocity_eq, hr.weak_gradient] with σ h1 h2
  obtain ⟨w, hw1, hw2⟩ := cross_profile_embed hd hp σ
  have hψ : IsTestField (φ σ) := ⟨Internal.TestPairing.slice_contDiff hφ.1 σ,
    Internal.TestPairing.slice_hasCompactSupport hR σ, hφ.2.2 σ⟩
  have hψ2 : MemLp (φ σ) 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hψ6 : MemLp (φ σ) 6 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hG : ∀ᵐ y, ∀ j : Fin 3, G σ y (unitVector j) =
      (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y :=
    ae_all_iff.2 fun j => partialX_ae_of_weakGradient h2 _ h1 j
  have hW2 : ∀ᵐ y, ∀ j : Fin 3, (partialX j w : Space → Space) y =
      fderiv ℝ (d.profile p σ) y (unitVector j) := ae_all_iff.2 hw2
  have key := cross_polarize w (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) hψ
  obtain ⟨K, hK⟩ := WeakProfile.Internal.AdvectionByParts.pairForm_bound hψ
  have eL : ∫ y, crossPart (d.profile p) v φ (σ, y) =
      -((∫ y, WeakProfile.Internal.AdvectionByParts.pairForm (φ σ) (velocity w)
          (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) y)
        + ∫ y, WeakProfile.Internal.AdvectionByParts.pairForm (φ σ)
          (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) (velocity w) y) := by
    rw [← integral_add (hK _ _).1 (hK _ _).1, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [h1, hw1] with y hy1 hy2
    exact cross_slice_left _ _ _ σ _ _ y hy1 hy2
  have eR : ∫ y, inner ℝ (G σ y (d.profile p σ y) + fderiv ℝ (d.profile p σ) y (v σ y)) (φ σ y) =
      trilinear w (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) (φ σ)
        + trilinear (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) w (φ σ) := by
    unfold trilinear
    rw [← integral_add (hC w _ _ hψ2 hψ6).1 (hC _ w _ hψ2 hψ6).1]
    refine integral_congr_ae ?_
    filter_upwards [h1, hw1, hG, hW2] with y hy1 hy2 hy3 hy4
    exact cross_slice_right (G σ y) (fderiv ℝ (d.profile p σ) y) (d.profile p σ y) (v σ y) (φ σ y)
      _ _ (fun j => (partialX j w : Space → Space))
      (fun j => (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space))
      y hy1 hy2 hy3 hy4
  calc _ = _ := eL
    _ = _ := congrArg Neg.neg key
    _ = _ := neg_neg _
    _ = _ := eR.symm

theorem cross_identity {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    Integrable (crossPart (d.profile p) v φ) ∧
    ∫ z, crossPart (d.profile p) v φ z = ∫ z : ℝ × Space, inner ℝ
      (G z.1 z.2 (d.profile p z.1 z.2) + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2) := by
  have h1 := cross_integrable hd hp hr hsup hφ
  have h2 := cross_conv_integrable hd hp hr hφ
  refine ⟨h1, ?_⟩
  rw [Measure.volume_eq_prod] at h1 h2 ⊢
  rw [integral_prod _ h1, integral_prod _ h2]
  exact integral_congr_ae (cross_slice hd hp hr hφ)

theorem quad_slice_test {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) (σ : ℝ) :
    IsTestField (φ σ) := by
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hφ.2.1
  exact ⟨Internal.TestPairing.slice_contDiff hφ.1 σ,
    Internal.TestPairing.slice_hasCompactSupport hR σ, hφ.2.2 σ⟩

theorem quad_column {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) (i : Fin 3) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector i)) ∧
    HasCompactSupport (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector i)) := by
  obtain ⟨hc, hs⟩ := test_fderiv hφ
  exact ⟨hc.clm_apply continuous_const,
    hs.comp_left (g := fun L : Space →L[ℝ] Space => L (unitVector i)) (by simp)⟩

theorem quad_reading {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) :
    IsReadingOf u (readingOf u).1 (readingOf u).2.1 (readingOf u).2.2 := by
  have hex : ∃ r : VelField × GradField × SecondField, IsReadingOf u r.1 r.2.1 r.2.2 :=
    ⟨(v, G, H), hr⟩
  unfold readingOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem quad_weight : IsAdmissibleWeight (fun _ : Space => (1 : ℝ)) 1 :=
  ⟨one_pos, measurable_const, fun _ => le_rfl, ⟨1, fun _ => le_rfl⟩⟩

theorem quad_point (L : Space →L[ℝ] Space) (w ψ a : Space) (c : Fin 3 → Space) (hw : w = a)
    (hc : ∀ j, L (unitVector j) = c j) :
    inner ℝ (L w) ψ = ∑ j : Fin 3, a j * inner ℝ (c j) ψ := by
  rw [Internal.Convection.apply_eq_sum_unitVector L w, sum_inner, hw]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, hc j]

theorem quad_slice {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ∀ᵐ σ : ℝ, ∫ y, quadPart v φ (σ, y) = ∫ y, inner ℝ (productField u u σ y) (φ σ y) := by
  have hR := quad_reading hr
  filter_upwards [hr.velocity_eq, hR.velocity_eq, hR.weak_gradient] with σ h1 h2 h3
  have hj : ∀ᵐ y, ∀ j : Fin 3, (readingOf u).2.1 σ y (unitVector j) =
      (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y :=
    ae_all_iff.2 fun j => Internal.Convection.partialX_ae_of_weakGradient h3 _ h2 j
  have hA := WeakProfile.advectionByParts_holds (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))
    (φ σ) (quad_slice_test hφ σ)
  have eL : ∫ y, quadPart v φ (σ, y) = -∫ y, ∑ i : Fin 3,
      (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y i *
      inner ℝ ((velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y)
        (fderiv ℝ (φ σ) y (unitVector i)) := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [h1] with y hy
    simp only [quadPart, hy]
  rw [eL, hA, neg_neg, trilinear]
  refine integral_congr_ae ?_
  filter_upwards [h2, hj] with y hy hy2
  exact (quad_point _ _ _ _ _ hy hy2).symm

theorem quad_identity {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) (hPB : ProductBoundHolds) :
    Integrable (quadPart v φ) ∧
    ∫ z, quadPart v φ z = ∫ z : ℝ × Space, inner ℝ (productField u u z.1 z.2) (φ z.1 z.2) := by
  have iQ : Integrable (quadPart v φ) := by
    have h : ∀ i : Fin 3, Integrable (fun z : ℝ × Space => (v z.1 z.2) i *
        inner ℝ (v z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i))) := fun i =>
      (velocity_local hr hsup (quad_column hφ i).1 (quad_column hφ i).2).2 i
    exact (integrable_finsetSum Finset.univ fun i _ => h i).neg
  have hF : IsPeriodicField (productField u u) := (hPB _ _ quad_weight u u hsup).1
  obtain ⟨R, -, hRb⟩ := Internal.TestPairing.exists_bound hφ.2.1
  have iP : Integrable (fun z : ℝ × Space => inner ℝ (productField u u z.1 z.2) (φ z.1 z.2)) :=
    Internal.TestPairing.integrable_pairing hF hφ.1 hφ.2.1 hRb
  refine ⟨iQ, ?_⟩
  have iQ' : Integrable (quadPart v φ) ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]; exact iQ
  have iP' : Integrable (fun z : ℝ × Space => inner ℝ (productField u u z.1 z.2) (φ z.1 z.2))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]; exact iP
  rw [Measure.volume_eq_prod, integral_prod _ iQ', integral_prod _ iP']
  exact integral_congr_ae (quad_slice hr hφ)

end Internal.HeldWeakEquation

open Internal.HeldWeakEquation

theorem heldWeakEquationHolds_of (h1 : FreePerturbationHolds) (h2 : ConvectionHolds)
    (h3 : DataHolds) (h4 : ProductPairingHolds) (_h5 : ProductBoundHolds)
    (_h6 : TestPairingHolds) : HeldWeakEquationHolds := by
  intro k d hd p hp f κ hf hκ v G H hr φ hφ
  have hP := hd.period_pos p hp
  obtain ⟨g, hg, hgφ⟩ := h1 d.symmetries (d.period p) hP f hf.invariant v G H hr
  have hsup : supGrad (freeInv (d.period p) f) < ⊤ := lt_of_le_of_lt hf.sup ENNReal.ofReal_lt_top
  obtain ⟨iB, iS, eB⟩ := bar_identity hd hp hφ
  have iA := actuator_integrable hd (d.multiplier p) hφ
  obtain ⟨iv, iG, ig⟩ := lin_integrable hr hsup hg hφ
  obtain ⟨iC, eC⟩ := cross_identity hd hp hr hsup hφ
  obtain ⟨iQ, eQ⟩ := quad_identity hr hsup hφ _h5
  have iL : Integrable (linPart (d.period p) v G φ) := iv.add iG
  have hsplit : sigmaSimilarityIntegrand (d.period p) (fun σ y => d.profile p σ y + v σ y)
      (fun σ y => fderiv ℝ (d.profile p σ) y + G σ y) φ = fun z =>
        barPart (d.period p) (d.profile p) φ z + linPart (d.period p) v G φ z
          + crossPart (d.profile p) v φ z + quadPart v φ z :=
    funext (integrand_split (d.period p) (d.profile p) v G φ)
  have iBL : Integrable (fun z => barPart (d.period p) (d.profile p) φ z
      + linPart (d.period p) v G φ z) := iB.add iL
  have iBLC : Integrable (fun z => barPart (d.period p) (d.profile p) φ z
      + linPart (d.period p) v G φ z + crossPart (d.profile p) v φ z) := iBL.add iC
  rw [hsplit]
  refine ⟨iBLC.add iQ, ?_⟩
  beta_reduce
  rw [integral_add iBLC iQ, integral_add iBL iC, integral_add iB iL]
  have eL : ∫ z, linPart (d.period p) v G φ z = inner ℝ f (testInHH φ) := by
    rw [← hgφ φ hφ]
    unfold linPart
    rw [integral_add iv iG, integral_add ig iG]
    congr 1
    exact hg.transport φ ⟨hφ.1, hφ.2.1⟩
  have eCv := (h2 d hd p hp).2.2 (freeInv (d.period p) f) v G H hr φ hφ
  have eD := (h3 d hd p hp).1 φ hφ
  have eAct := (h3 d hd p hp).2.2.1 κ φ hφ
  have eP := h4 (freeInv (d.period p) f) (freeInv (d.period p) f) hsup φ hφ
  have heq := congrArg (fun x => inner ℝ x (testInHH φ)) hf.equation
  simp only [inner_add_left, inner_zero_left] at heq
  have hκ' : κ = -d.multiplier p := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hκ
  have eAct' : ∫ z : ℝ × Space, inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2) =
      -∫ z : ℝ × Space, inner ℝ (∑ i, d.multiplier p i • d.actuator i z.1 z.2) (φ z.1 z.2) := by
    rw [← integral_neg]
    congr 1
    funext z
    simp only [hκ', Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, inner_neg_left]
  have eDs : ∫ z : ℝ × Space, inner ℝ (defectField (d.period p) (d.profile p) (d.pressure p)
        d.actuator (d.multiplier p) z.1 z.2) (φ z.1 z.2) =
      (∫ z : ℝ × Space, inner ℝ (defectField (d.period p) (d.profile p) (d.pressure p)
        d.actuator 0 z.1 z.2) (φ z.1 z.2)) +
      ∫ z : ℝ × Space, inner ℝ (∑ i, d.multiplier p i • d.actuator i z.1 z.2) (φ z.1 z.2) := by
    rw [← integral_add iS iA]
    congr 1
    funext z
    rw [defect_split, inner_add_left]
  linarith

end Breakdown.Cert
