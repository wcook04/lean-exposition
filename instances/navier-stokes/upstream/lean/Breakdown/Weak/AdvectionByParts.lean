import Breakdown.Weak.StatementsSlice
import Breakdown.FreqTr.WeakInX
import Breakdown.FreqTr.PairingByParts
import Breakdown.FreqTr.Advection

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.AdvectionByParts

def pairForm (ψ a b : Space → Space) (y : Space) : ℝ :=
  ∑ i : Fin 3, a y i * inner ℝ (b y) (fderiv ℝ ψ y (unitVector i))

theorem lintegral_three_le {f g h : Space → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hh : AEMeasurable h volume) :
    ∫⁻ x, f x * g x * h x ≤
      (∫⁻ x, f x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) * (∫⁻ x, g x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) *
        (∫⁻ x, h x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := volume) (Finset.univ : Finset (Fin 3))
    (f := ![fun x => f x ^ (6 : ℝ), fun x => g x ^ (6 : ℝ), fun x => h x ^ (3 / 2 : ℝ)])
    (p := ![1 / 6, 1 / 6, 2 / 3])
    (by
      intro i _
      fin_cases i
      · exact hf.pow_const _
      · exact hg.pow_const _
      · exact hh.pow_const _)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by intro i _; fin_cases i <;> norm_num)
  simp only [Fin.prod_univ_three, Matrix.cons_val] at key
  refine le_trans (le_of_eq ?_) key
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_enorm_three_le {a b c : Space → Space} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) (hc : AEStronglyMeasurable c volume) :
    ∫⁻ x, ‖a x‖ₑ * ‖b x‖ₑ * ‖c x‖ₑ ≤
      eLpNorm a 6 volume * eLpNorm b 6 volume * (∫⁻ x, ‖c x‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
  refine (lintegral_three_le ha.enorm hb.enorm hc.enorm).trans (le_of_eq ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := a) (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (f := b) (by norm_num) (by norm_num)]
  norm_num

theorem lintegral_rpow_ne_top {c : Space → Space} (hc : Continuous c) (hs : HasCompactSupport c) :
    (∫⁻ x, ‖c x‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≠ ⊤ := by
  have hm : MemLp c (ENNReal.ofReal (3 / 2)) volume := hc.memLp_of_hasCompactSupport hs
  have h1 := hm.eLpNorm_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rw [Ne, ENNReal.ofReal_eq_zero]; norm_num)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by norm_num)] at h1
  have h2 : ∫⁻ x, ‖c x‖ₑ ^ (3 / 2 : ℝ) ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos (by norm_num)] at h1
    exact h1 rfl
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) h2

theorem enorm_sum_le (a b : Space) (c : Fin 3 → Space) :
    ‖∑ i : Fin 3, a i * inner ℝ b (c i)‖ₑ ≤ ∑ i : Fin 3, ‖a‖ₑ * ‖b‖ₑ * ‖c i‖ₑ := by
  rw [← ofReal_norm]
  have hn : ‖∑ i : Fin 3, a i * inner ℝ b (c i)‖ ≤ ∑ i : Fin 3, ‖a‖ * ‖b‖ * ‖c i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (PiLp.norm_apply_le a i) (norm_inner_le_norm _ _) (norm_nonneg _)
      (norm_nonneg _)
  refine (ENNReal.ofReal_le_ofReal hn).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
    ofReal_norm, ofReal_norm]

theorem pairForm_bound {ψ : Space → Space} (hψ : IsTestField ψ) : ∃ K : ℝ, ∀ a b : L6R,
    Integrable (pairForm ψ a b) ∧ |∫ y, pairForm ψ a b y| ≤ K * ‖a‖ * ‖b‖ := by
  obtain ⟨hψs, hψc, -⟩ := hψ
  have hcc : ∀ i : Fin 3, Continuous (fun y => fderiv ℝ ψ y (unitVector i)) :=
    fun i => (hψs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : ∀ i : Fin 3, HasCompactSupport (fun y => fderiv ℝ ψ y (unitVector i)) :=
    fun i => hψc.fderiv_apply (𝕜 := ℝ) _
  have hKt : ∀ i : Fin 3,
      (∫⁻ y, ‖fderiv ℝ ψ y (unitVector i)‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≠ ⊤ :=
    fun i => lintegral_rpow_ne_top (hcc i) (hcs i)
  refine ⟨∑ i : Fin 3,
    ((∫⁻ y, ‖fderiv ℝ ψ y (unitVector i)‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)).toReal, fun a b => ?_⟩
  have ha : AEStronglyMeasurable (a : Space → Space) volume := Lp.aestronglyMeasurable _
  have hb : AEStronglyMeasurable (b : Space → Space) volume := Lp.aestronglyMeasurable _
  have hlin : ∫⁻ y, ‖pairForm ψ a b y‖ₑ ≤ ∑ i : Fin 3,
      eLpNorm (a : Space → Space) 6 volume * eLpNorm (b : Space → Space) 6 volume *
        (∫⁻ y, ‖fderiv ℝ ψ y (unitVector i)‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    refine (lintegral_mono fun y => enorm_sum_le ((a : Space → Space) y) ((b : Space → Space) y)
      (fun i => fderiv ℝ ψ y (unitVector i))).trans ?_
    rw [lintegral_finsetSum' (f := fun i y => ‖(a : Space → Space) y‖ₑ * ‖(b : Space → Space) y‖ₑ *
      ‖fderiv ℝ ψ y (unitVector i)‖ₑ) _ (fun i _ =>
      (ha.enorm.mul hb.enorm).mul (hcc i).aestronglyMeasurable.enorm)]
    exact Finset.sum_le_sum fun i _ => lintegral_enorm_three_le ha hb (hcc i).aestronglyMeasurable
  have hfin : (∑ i : Fin 3,
      eLpNorm (a : Space → Space) 6 volume * eLpNorm (b : Space → Space) 6 volume *
        (∫⁻ y, ‖fderiv ℝ ψ y (unitVector i)‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)) (hKt i)
  have hF : AEStronglyMeasurable (pairForm ψ a b) volume := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable ha).mul
      (hb.inner (hcc i).aestronglyMeasurable)
  refine ⟨⟨hF, lt_of_le_of_lt hlin hfin.lt_top⟩, ?_⟩
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine (ENNReal.toReal_mono hfin (by simpa only [ofReal_norm] using hlin)).trans (le_of_eq ?_)
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.1 hfin i (Finset.mem_univ i)),
    Lp.norm_def, Lp.norm_def, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

theorem pairForm_sub_left {ψ : Space → Space} (hψ : IsTestField ψ) (a a' b : L6R) :
    ∫ y, pairForm ψ (a - a' : L6R) b y = (∫ y, pairForm ψ a b y) - ∫ y, pairForm ψ a' b y := by
  obtain ⟨K, hK⟩ := pairForm_bound hψ
  refine (integral_congr_ae ?_).trans (integral_sub (hK a b).1 (hK a' b).1)
  filter_upwards [Lp.coeFn_sub a a'] with y hy
  simp only [pairForm, hy, Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem pairForm_sub_right {ψ : Space → Space} (hψ : IsTestField ψ) (a b b' : L6R) :
    ∫ y, pairForm ψ a (b - b' : L6R) y = (∫ y, pairForm ψ a b y) - ∫ y, pairForm ψ a b' y := by
  obtain ⟨K, hK⟩ := pairForm_bound hψ
  refine (integral_congr_ae ?_).trans (integral_sub (hK a b).1 (hK a b').1)
  filter_upwards [Lp.coeFn_sub b b'] with y hy
  simp only [pairForm, hy, Pi.sub_apply, inner_sub_left, mul_sub, Finset.sum_sub_distrib]

def diagForm (ψ : Space → Space) (a : L6R) : ℝ := ∫ y, pairForm ψ a a y

theorem continuous_diagForm {ψ : Space → Space} (hψ : IsTestField ψ) :
    Continuous (diagForm ψ) := by
  obtain ⟨K, hK⟩ := pairForm_bound hψ
  rw [continuous_iff_continuousAt]
  intro a0
  have key : ∀ a : L6R, dist (diagForm ψ a) (diagForm ψ a0) ≤
      K * ‖a - a0‖ * ‖a‖ + K * ‖a0‖ * ‖a - a0‖ := by
    intro a
    have h1 := pairForm_sub_left hψ a a0 a
    have h2 := pairForm_sub_right hψ a0 a a0
    have e : diagForm ψ a - diagForm ψ a0 =
        (∫ y, pairForm ψ (a - a0 : L6R) a y) + ∫ y, pairForm ψ a0 (a - a0 : L6R) y := by
      unfold diagForm
      linarith
    rw [Real.dist_eq, e]
    exact (abs_add_le _ _).trans (add_le_add (hK _ _).2 (hK _ _).2)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero
    (g := fun a : L6R => K * ‖a - a0‖ * ‖a‖ + K * ‖a0‖ * ‖a - a0‖)
    (fun _ => dist_nonneg) key ?_)
  have hc : Continuous (fun a : L6R => K * ‖a - a0‖ * ‖a‖ + K * ‖a0‖ * ‖a - a0‖) := by
    fun_prop
  simpa using hc.tendsto a0

theorem fderiv_coord_smul {χ : Space → Space} (hχ : ContDiff ℝ ∞ χ) (i : Fin 3) (y v : Space) :
    fderiv ℝ (fun z => χ z i • χ z) y v = χ y i • fderiv ℝ χ y v + (fderiv ℝ χ y v) i • χ y := by
  have hd : DifferentiableAt ℝ χ y := hχ.differentiable (by simp) y
  have hp : HasFDerivAt (fun z => χ z i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ χ y)) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt
  change fderiv ℝ ((fun z => χ z i) • χ) y v = _
  rw [(hp.smul hd.hasFDerivAt).fderiv]
  simp

theorem smooth_by_parts {χ ψ : Space → Space} (hχ : IsTestField χ) (hψ : IsTestField ψ) :
    ∫ y, ∑ i : Fin 3, χ y i * inner ℝ (χ y) (fderiv ℝ ψ y (unitVector i)) =
      -advectionPairing χ ψ := by
  obtain ⟨hχs, -, hχd⟩ := hχ
  obtain ⟨hψs, hψc, -⟩ := hψ
  have hfi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z => χ z i • χ z) := fun i =>
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hχs).smul hχs
  have I1 : ∀ i : Fin 3, Integrable (fun y =>
      inner ℝ (fderiv ℝ (fun z => χ z i • χ z) y (unitVector i)) (ψ y)) := fun i =>
    Internal.PairingByParts.integrable_inner_of_compact
      (Internal.PairingByParts.dirDeriv_contDiff (hfi i) _).continuous hψs.continuous hψc
  have I2 : ∀ i : Fin 3, Integrable (fun y =>
      inner ℝ (χ y i • χ y) (fderiv ℝ ψ y (unitVector i))) := fun i =>
    Internal.PairingByParts.integrable_inner_of_compact (hfi i).continuous
      (Internal.PairingByParts.dirDeriv_contDiff hψs _).continuous (hψc.fderiv_apply (𝕜 := ℝ) _)
  have key : ∀ i : Fin 3, ∫ y, inner ℝ (χ y i • χ y) (fderiv ℝ ψ y (unitVector i)) =
      -∫ y, inner ℝ (fderiv ℝ (fun z => χ z i • χ z) y (unitVector i)) (ψ y) := by
    intro i
    have k := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
      (B := innerSL ℝ) (f := fun z => χ z i • χ z) (g := ψ) (v := unitVector i)
      (I1 i) (I2 i)
      (Internal.PairingByParts.integrable_inner_of_compact (hfi i).continuous hψs.continuous hψc)
      (fun y _ => (hfi i).differentiable (by simp) y)
      (fun y _ => hψs.differentiable (by simp) y)
    exact k
  have hpt : ∀ y, ∑ i : Fin 3,
      inner ℝ (fderiv ℝ (fun z => χ z i • χ z) y (unitVector i)) (ψ y) =
        inner ℝ (advectionAt χ y) (ψ y) := by
    intro y
    simp_rw [fderiv_coord_smul hχs, inner_add_left, real_inner_smul_left, Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
    have hdiv : ∑ i : Fin 3, (fderiv ℝ χ y (unitVector i)) i = 0 := hχd y
    rw [hdiv, zero_mul, add_zero, advectionAt]
    exact Internal.Advection.sum_coord_inner (fderiv ℝ χ y) (χ y) (ψ y)
  unfold advectionPairing
  calc ∫ y, ∑ i : Fin 3, χ y i * inner ℝ (χ y) (fderiv ℝ ψ y (unitVector i))
      = ∑ i : Fin 3, ∫ y, inner ℝ (χ y i • χ y) (fderiv ℝ ψ y (unitVector i)) := by
        rw [← integral_finsetSum _ (fun i _ => I2 i)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
          simp only [real_inner_smul_left])
    _ = ∑ i : Fin 3, -∫ y, inner ℝ (fderiv ℝ (fun z => χ z i • χ z) y (unitVector i)) (ψ y) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = -∫ y, inner ℝ (advectionAt χ y) (ψ y) := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => I1 i)]
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end Internal.AdvectionByParts

open Internal.AdvectionByParts in
theorem advectionByParts_holds : AdvectionByParts := by
  intro x ψ hψ
  have hψ2 : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hψ6 : MemLp ψ 6 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hT := Internal.WeakInX.continuous_trilinear_diag trilinear_holds ψ hψ2 hψ6
  have hF : Continuous (fun x : X => diagForm ψ (velocity x)) :=
    (continuous_diagForm hψ).comp velocity.continuous
  have hS : IsClosed {x : X | diagForm ψ (velocity x) = -trilinear x x ψ} :=
    isClosed_eq hF hT.neg
  have hsub : (testSpan : Set X) ⊆ {x : X | diagForm ψ (velocity x) = -trilinear x x ψ} := by
    intro z hz
    obtain ⟨χ, hχ, rfl⟩ := testSpan_holds z hz
    have hχd := isDecayField_of_isTestField hχ
    show diagForm ψ (velocity (embedX χ)) = -trilinear (embedX χ) (embedX χ) ψ
    unfold diagForm
    rw [← advectionTrilinear velocityDecay_holds partial_holds.1 χ ψ hχd hψ,
      ← smooth_by_parts hχ hψ]
    refine integral_congr_ae ?_
    filter_upwards [velocityDecay_holds χ hχd] with y hy
    simp only [pairForm, hy]
  have hcl := hS.closure_subset_iff.2 hsub
  rw [testDense_holds.2.closure_eq] at hcl
  exact hcl (mem_univ x)

end Breakdown.WeakProfile
