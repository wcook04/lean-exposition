import Breakdown.Frac.StRealize
import Breakdown.FreqTr.EmbedDilate
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal

open Breakdown.Freq Breakdown.Freq.Internal.EmbedDilate

theorem hasFDerivAt_ampScaled {f : Space → Space} (hf : Differentiable ℝ f) (a s : ℝ) (y : Space) :
    HasFDerivAt (fun y => a • f (s • y)) ((a * s) • fderiv ℝ f (s • y)) y := by
  have h := ((hf (s • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul s)).const_smul a
  have e : a • (fderiv ℝ f (s • y)).comp (s • ContinuousLinearMap.id ℝ Space) =
      (a * s) • fderiv ℝ f (s • y) := by
    ext v
    simp [smul_smul]
  rw [e] at h
  exact h

theorem one_add_le {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) : 1 + r ≤ (1 + s⁻¹) * (1 + s * r) := by
  have h1 : s⁻¹ * (s * r) = r := by field_simp
  have h2 : 0 ≤ s⁻¹ := (inv_pos.2 hs).le
  nlinarith [mul_nonneg hs.le hr]

theorem ampScaled_bound {a s C r : ℝ} (ha : 0 < a) (hs : 0 < s) (hC : 0 ≤ C) (hr : 0 ≤ r) :
    a * (C / (1 + s * r)) ≤ (a * (1 + s⁻¹) * C + a * s * (1 + s⁻¹) ^ 2 * C) / (1 + r) ∧
      a * s * (C / (1 + s * r) ^ 2) ≤
        (a * (1 + s⁻¹) * C + a * s * (1 + s⁻¹) ^ 2 * C) / (1 + r) ^ 2 := by
  have hp : 0 < 1 + s * r := by positivity
  have hq : 0 < 1 + r := by positivity
  have hK : 0 < 1 + s⁻¹ := by positivity
  have key := one_add_le hs hr
  have sq : (1 + r) ^ 2 ≤ ((1 + s⁻¹) * (1 + s * r)) ^ 2 := pow_le_pow_left₀ hq.le key 2
  have hA : 0 ≤ a * (1 + s⁻¹) * C := by positivity
  have hB : 0 ≤ a * s * (1 + s⁻¹) ^ 2 * C := by positivity
  constructor
  · have step : a * (C / (1 + s * r)) ≤ a * (1 + s⁻¹) * C / (1 + r) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hp hq]
      have := mul_le_mul_of_nonneg_left key (mul_nonneg ha.le hC)
      nlinarith [this]
    refine step.trans ?_
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  · have hr1 : 1 ≤ 1 + r := by linarith
    have step : a * s * (C / (1 + s * r) ^ 2) ≤ a * s * (1 + s⁻¹) ^ 2 * C / (1 + r) ^ 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left sq (mul_nonneg (mul_nonneg ha.le hs.le) hC)
      nlinarith [this]
    refine step.trans ?_
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem isDecayField_ampScaled {f : Space → Space} (hf : IsDecayField f) {a s : ℝ} (ha : 0 < a)
    (hs : 0 < s) : IsDecayField (fun y => a • f (s • y)) := by
  obtain ⟨hcd, hdiv, C, hC⟩ := hf
  have hdiff : Differentiable ℝ f := hcd.differentiable (by simp)
  have hfd : ∀ y, fderiv ℝ (fun y => a • f (s • y)) y = (a * s) • fderiv ℝ f (s • y) :=
    fun y => (hasFDerivAt_ampScaled hdiff a s y).fderiv
  have hC0 : 0 ≤ C := by
    have := (hC 0).1
    simp only [norm_zero, add_zero, div_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨(hcd.comp (contDiff_id.const_smul s)).const_smul a, fun y => ?_,
    a * (1 + s⁻¹) * C + a * s * (1 + s⁻¹) ^ 2 * C, fun y => ?_⟩
  · simp only [divergenceAt, hfd, FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
      ← Finset.mul_sum]
    have := hdiv (s • y)
    simp only [divergenceAt] at this
    rw [this, mul_zero]
  · have hn : ‖s • y‖ = s * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
    obtain ⟨b1, b2⟩ := ampScaled_bound ha hs hC0 (norm_nonneg y)
    obtain ⟨c1, c2⟩ := hC (s • y)
    rw [hn] at c1 c2
    constructor
    · rw [norm_smul, Real.norm_of_nonneg ha.le]
      exact (mul_le_mul_of_nonneg_left c1 ha.le).trans b1
    · rw [hfd, norm_smul, Real.norm_of_nonneg (mul_nonneg ha.le hs.le)]
      exact (mul_le_mul_of_nonneg_left c2 (mul_nonneg ha.le hs.le)).trans b2

theorem partialField_ampScaled {f : Space → Space} (hf : IsDecayField f) (a s : ℝ) (k : Fin 3) :
    partialField (fun y => a • f (s • y)) k = fun y => (a * s) • partialField f k (s • y) := by
  funext y
  have hdiff : Differentiable ℝ f := hf.1.differentiable (by simp)
  show fderiv ℝ (fun y => a • f (s • y)) y (unitVector k) = _
  rw [(hasFDerivAt_ampScaled hdiff a s y).fderiv]
  rfl

theorem complexify_ampScaled {f : Space → Space} (hf : IsDecayField f) {a s : ℝ} (ha : 0 < a)
    (hs : 0 < s) (k : Fin 3) :
    complexify (toLpOrZero 2 (partialField (fun y => a • f (s • y)) k)) =
      (a * s) • scaleOp s (complexify (toLpOrZero 2 (partialField f k))) := by
  have m1 := memLp_partialField hf k
  have m2 := memLp_partialField (isDecayField_ampScaled hf ha hs) k
  simp only [toLpOrZero, dif_pos m1, dif_pos m2]
  unfold complexify
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (m2.toLp _),
    m2.coeFn_toLp,
    Lp.coeFn_smul (a * s) (scaleOp s (ContinuousLinearMap.compLpL 2 volume complexifyVec (m1.toLp _))),
    scaleOp_ae fieldOpRealized_holds hs.ne' (ContinuousLinearMap.compLpL 2 volume complexifyVec (m1.toLp _)),
    ae_comp_smul hs.ne' (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (m1.toLp _)),
    ae_comp_smul hs.ne' m1.coeFn_toLp] with ξ h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, h₃, Pi.smul_apply, h₄, h₅, h₆, partialField_ampScaled hf a s k]
  exact map_smul complexifyVec (a * s) _

theorem gradHat_ampScaled {f : Space → Space} (hf : IsDecayField f) {a s : ℝ} (ha : 0 < a)
    (hs : 0 < s) (k : Fin 3) :
    gradHat (fun y => a • f (s • y)) k = (a * s⁻¹ * s⁻¹) • scaleOp s⁻¹ (gradHat f k) := by
  unfold gradHat
  rw [complexify_ampScaled hf ha hs k, map_smul, freqTr_scaleOp fieldOpRealized_holds hs.ne',
    smul_smul]
  congr 1
  rw [abs_of_pos (by positivity)]
  field_simp

theorem ofGrad_ampScaled {f : Space → Space} (hf : IsDecayField f) {a s : ℝ} (ha : 0 < a)
    (hs : 0 < s) :
    ofGrad (fun y => a • f (s • y)) = (a * s⁻¹ * s⁻¹) • scaleOp s⁻¹ (ofGrad f) := by
  change ∑ k : Fin 3, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (gradHat (fun y => a • f (s • y)) k) =
    (a * s⁻¹ * s⁻¹) • scaleOp s⁻¹
      (∑ k : Fin 3, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (gradHat f k))
  simp only [gradHat_ampScaled hf ha hs, map_smul, mult_scaleOp fieldOpRealized_holds _ (inv_pos.2 hs),
    map_sum, Finset.smul_sum]

theorem fracDilL2_eq (α : ℝ) {μ : ℝ} (hμ : 0 < μ) (g : L2C) :
    fracDilL2 α μ g = (μ ^ (1 - 3 / (2 * α))) • scaleOp (μ ^ (-(1 / (2 * α)))) g := by
  have hc : μ ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  have := fieldOpRealized_holds (scaleEquiv _ hc)
    (fun _ => (μ ^ (1 - 3 / (2 * α))) • ContinuousLinearMap.id ℝ CSpace)
    ‖μ ^ (1 - 3 / (2 * α))‖ aestronglyMeasurable_const
    (fun _ => by rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le) g
  rw [scaleEquiv_coe] at this
  unfold fracDilL2
  apply Lp.ext
  filter_upwards [this, Lp.coeFn_smul (μ ^ (1 - 3 / (2 * α))) (scaleOp (μ ^ (-(1 / (2 * α)))) g),
    scaleOp_ae fieldOpRealized_holds hc g] with ξ h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃]
  rfl

theorem ofGrad_scaleField (α : ℝ) {f : Space → Space} (hf : IsDecayField f) {μ : ℝ} (hμ : 0 < μ) :
    ofGrad (scaleField α μ f) = fracDilL2 α μ (ofGrad f) := by
  have hs : 0 < μ ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  have ha : 0 < μ ^ (1 - 1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  rw [fracDilL2_eq α hμ]
  unfold scaleField
  rw [ofGrad_ampScaled hf ha hs]
  have e1 : (μ ^ (1 / (2 * α)))⁻¹ = μ ^ (-(1 / (2 * α))) := (Real.rpow_neg hμ.le _).symm
  have e2 : μ ^ (1 - 1 / (2 * α)) * (μ ^ (1 / (2 * α)))⁻¹ * (μ ^ (1 / (2 * α)))⁻¹ =
      μ ^ (1 - 3 / (2 * α)) := by
    rw [e1, ← Real.rpow_add hμ, ← Real.rpow_add hμ]
    congr 1
    ring
  rw [e2, e1]

end Breakdown.FracInternal

namespace Breakdown.Freq

theorem decayFieldScale (α : ℝ) (hα : 0 < α) : DecayFieldScale α := by
  intro μ f hμ hf
  exact FracInternal.isDecayField_ampScaled hf (Real.rpow_pos_of_pos hμ _) (Real.rpow_pos_of_pos hμ _)

theorem fracEmbedDilate (α : ℝ) (hα : 0 < α) (h1 : FracDilationAlgebra α) (h2 : DecayFieldScale α) :
    FracEmbedDilate α := by
  intro μ f hμ hf
  have hd := h2 μ f hμ hf
  apply Subtype.ext
  rw [h1.2.2.2.2 μ hμ]
  simp only [embedX, dif_pos (embedMem_holds f hf), dif_pos (embedMem_holds _ hd)]
  exact (FracInternal.ofGrad_scaleField α hf hμ).symm

end Breakdown.Freq
