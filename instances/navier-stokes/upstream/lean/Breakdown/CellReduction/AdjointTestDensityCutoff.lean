import Breakdown.CellReduction.AdjointStatements
import Breakdown.CertCell.ActuatorPairingDensity
import Breakdown.CertCell.TailSquareSmoothing

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal.TestDensity

open CertCell.Internal.ActuatorPairingDensity

attribute [local instance] CertCell.Internal.ActuatorPairingDensity.prodVolume_addInvariant
attribute [local instance] CertCell.Internal.ActuatorPairingDensity.prodVolume_isNegInvariant

theorem slice_hasSpaceDeriv {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (s : ℝ) (y : Space) :
    HasFDerivAt (F s) ((fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (s, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space)) y := by
  have h1 : HasFDerivAt (fun z : ℝ × Space => F z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (s, y)) (s, y) :=
    (hF.differentiable one_ne_zero (s, y)).hasFDerivAt
  exact h1.comp y (hasFDerivAt_prodMk_right s y)

theorem time_hasDerivAt {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (s : ℝ) (y : Space) :
    HasDerivAt (fun s' => F s' y) (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (s, y) ((1 : ℝ), (0 : Space))) s := by
  have h1 : HasFDerivAt (fun z : ℝ × Space => F z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (s, y)) (s, y) :=
    (hF.differentiable one_ne_zero (s, y)).hasFDerivAt
  have h2 : HasDerivAt (fun s' : ℝ => ((s', y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact h1.comp_hasDerivAt s h2

theorem time_hasDerivAt' {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (s : ℝ) (y : Space) : HasDerivAt (fun s' => F s' y) (timeDerivative F s y) s :=
  (time_hasDerivAt hF s y).differentiableAt.hasDerivAt

theorem slice_spaceDeriv_continuous {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) = fun z =>
      (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact (slice_hasSpaceDeriv hF z.1 z.2).fderiv
  rw [e]
  exact (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem time_deriv_continuous {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    Continuous (fun z : ℝ × Space => timeDerivative F z.1 z.2) := by
  have e : (fun z : ℝ × Space => timeDerivative F z.1 z.2) = fun z =>
      fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) z ((1 : ℝ), (0 : Space)) := by
    funext z
    exact (time_hasDerivAt hF z.1 z.2).deriv
  rw [e]
  exact (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem kernel_ne_norm_lt {m : ℕ} {w : ℝ × Space} (h : kernel m w ≠ 0) : ‖w‖ < 1 := by
  have hmem : w ∈ Function.support ((bumpSeq m).normed volume) := h
  rw [(bumpSeq m).support_normed_eq, Metric.mem_ball, dist_zero_right] at hmem
  have h1 : (bumpSeq m).rOut ≤ 1 := by
    show 1 / ((m : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  linarith

theorem kernel_integral_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ)
    {K : ℝ × Space → E} {z : ℝ × Space} {B : ℝ}
    (hB : ∀ w : ℝ × Space, ‖w‖ < 1 → ‖K (z - w)‖ ≤ B) : ‖∫ w, kernel m w • K (z - w)‖ ≤ B := by
  refine (norm_integral_le_of_norm_le ((kernel_integrable m).mul_const B) (ae_of_all _ fun w => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg m w)]
    by_cases hw : kernel m w = 0
    · rw [hw, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hB w (kernel_ne_norm_lt hw)) (kernel_nonneg m w)
  · rw [integral_mul_const, kernel_integral, one_mul]

theorem smoothed_time_hasDerivAt {h : ℝ → Space → Space} (hh : ContDiff ℝ 1 (fun z : ℝ × Space => h z.1 z.2))
    {C Ct : ℝ} (hC : ∀ σ y, ‖h σ y‖ ≤ C) (hCt : ∀ σ y, ‖timeDerivative h σ y‖ ≤ Ct) (m : ℕ)
    (σ : ℝ) (y : Space) :
    HasDerivAt (fun s => smoothed h m s y)
      (∫ w : ℝ × Space, kernel m w • timeDerivative h (σ - w.1) (y - w.2)) σ := by
  have e : (fun s => smoothed h m s y) = fun s => ∫ w : ℝ × Space, kernel m w • h (s - w.1) (y - w.2) :=
    funext fun s => smoothed_eq h m s y
  rw [e]
  have hc : Continuous (fun z : ℝ × Space => h z.1 z.2) := hh.continuous
  have ht := time_deriv_continuous hh
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (s := Set.univ)
    (bound := fun w => kernel m w * Ct)
    (F := fun s w => kernel m w • h (s - w.1) (y - w.2))
    (F' := fun s w => kernel m w • timeDerivative h (s - w.1) (y - w.2)) Filter.univ_mem
    (Filter.Eventually.of_forall fun s =>
      (integrable_kernel_smul m hc (fun z => hC z.1 z.2) (s, y)).aestronglyMeasurable)
    (integrable_kernel_smul m hc (fun z => hC z.1 z.2) (σ, y)) ?_ (ae_of_all _ fun w s _ => ?_)
    ((kernel_integrable m).mul_const Ct) (ae_of_all _ fun w s _ => ?_)).2
  · exact (integrable_kernel_smul m ht (fun z => hCt z.1 z.2) (σ, y)).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg m w)]
    exact mul_le_mul_of_nonneg_left (hCt _ _) (kernel_nonneg m w)
  · have h1 : HasDerivAt (fun s' : ℝ => s' - w.1) 1 s := (hasDerivAt_id s).sub_const w.1
    have h2 := ((time_hasDerivAt' hh (s - w.1) (y - w.2)).scomp s h1).const_smul (kernel m w)
    rw [one_smul] at h2
    exact h2

theorem smoothed_timeDerivative {h : ℝ → Space → Space} (hh : ContDiff ℝ 1 (fun z : ℝ × Space => h z.1 z.2))
    {C Ct : ℝ} (hC : ∀ σ y, ‖h σ y‖ ≤ C) (hCt : ∀ σ y, ‖timeDerivative h σ y‖ ≤ Ct) (m : ℕ)
    (σ : ℝ) (y : Space) :
    timeDerivative (smoothed h m) σ y = ∫ w : ℝ × Space, kernel m w • timeDerivative h (σ - w.1) (y - w.2) :=
  (smoothed_time_hasDerivAt hh hC hCt m σ y).deriv

theorem kernel_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : ℝ × Space → E} (hc : Continuous K) (hs : HasCompactSupport K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m in atTop, ∀ z, ‖(∫ w, kernel m w • K (z - w)) - K z‖ ≤ δ := by
  obtain ⟨η, hη, hK⟩ := Metric.uniformContinuous_iff.1 (hs.uniformContinuous_of_continuous hc) δ hδ
  filter_upwards [rOut_tendsto.eventually (gt_mem_nhds hη)] with m hm z
  have h := (bumpSeq m).dist_normed_convolution_le (μ := volume) (x₀ := z) (ε := δ) hc.aestronglyMeasurable
    (fun x hx => (hK (lt_trans (Metric.mem_ball.1 hx) hm)).le)
  have e : (∫ w, kernel m w • K (z - w)) =
      convolution ((bumpSeq m).normed volume) K (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    rw [convolution_def]
    rfl
  rw [e, ← dist_eq_norm]
  exact h

theorem frac_antitone {a t q r : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t) (hqr : q ≤ r) : a / t ^ r ≤ a / t ^ q :=
  div_le_div_of_nonneg_left ha (Real.rpow_pos_of_pos (by linarith) q) (Real.rpow_le_rpow_of_exponent_le ht hqr)

theorem frac_mul {a b t q r : ℝ} (ht : 0 < t) : a / t ^ q * (b / t ^ r) = a * b / t ^ (q + r) := by
  rw [Real.rpow_add ht]
  have h1 : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  have h2 : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  field_simp

theorem frac_shift {K q : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q) (y w : Space) (hw : ‖w‖ ≤ 1) :
    K / (1 + ‖y - w‖) ^ q ≤ 2 ^ q * K / (1 + ‖y‖) ^ q := by
  have h0 := norm_sub_norm_le y w
  have h1 : (1 + ‖y‖) / 2 ≤ 1 + ‖y - w‖ := by
    have := norm_nonneg (y - w)
    linarith
  have hpos : 0 < (1 + ‖y‖) / 2 := by positivity
  have h2 : ((1 + ‖y‖) / 2) ^ q ≤ (1 + ‖y - w‖) ^ q := Real.rpow_le_rpow hpos.le h1 hq
  rw [Real.div_rpow (by positivity) (by norm_num)] at h2
  have h3 : 0 < (1 + ‖y‖) ^ q := Real.rpow_pos_of_pos (by positivity) q
  have h4 : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  calc K / (1 + ‖y - w‖) ^ q ≤ K / ((1 + ‖y‖) ^ q / 2 ^ q) :=
        div_le_div_of_nonneg_left hK (by positivity) h2
    _ = 2 ^ q * K / (1 + ‖y‖) ^ q := by field_simp

open CertCell.TailBand.SquareInternal (roundBump roundBump_contDiff roundBump_hasCompactSupport roundBump_eq_one
  roundBump_eq_zero roundBump_nonneg roundBump_le_one scaledBump scaledBump_contDiff scaledBump_eq_one scaledBump_eq_zero)

def crossGrad : (Space →L[ℝ] ℝ) →L[ℝ] Space →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ ℝ (unitVector 1)).smulRight
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 0))
    - (ContinuousLinearMap.apply ℝ ℝ (unitVector 2)).smulRight
      ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 0))
    + (ContinuousLinearMap.apply ℝ ℝ (unitVector 2)).smulRight
      ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1))
    - (ContinuousLinearMap.apply ℝ ℝ (unitVector 0)).smulRight
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1))
    + (ContinuousLinearMap.apply ℝ ℝ (unitVector 0)).smulRight
      ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 2))
    - (ContinuousLinearMap.apply ℝ ℝ (unitVector 1)).smulRight
      ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 2))

theorem crossGrad_comp (L : Space →L[ℝ] ℝ) (a : Space) (i : Fin 3) :
    crossGrad L a i = if i = 0 then L (unitVector 1) * a 2 - L (unitVector 2) * a 1
      else if i = 1 then L (unitVector 2) * a 0 - L (unitVector 0) * a 2
      else L (unitVector 0) * a 1 - L (unitVector 1) * a 0 := by
  fin_cases i <;> simp [crossGrad, unitVector]

theorem eq_zero_of_eventually {f : Space → ℝ} {c : ℝ} {x : Space} (h : f =ᶠ[𝓝 x] fun _ => c) :
    fderiv ℝ f x = 0 := by
  rw [h.fderiv_eq]
  exact fderiv_const_apply c

theorem round_spaceDeriv_far {x : Space} (hx : 2 < ‖x‖) : fderiv ℝ roundBump x = 0 := by
  refine eq_zero_of_eventually (c := 0) ?_
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with x' hx'
  exact roundBump_eq_zero (le_of_lt hx')

theorem round_spaceDeriv2_far {x : Space} (hx : 2 < ‖x‖) : fderiv ℝ (fderiv ℝ roundBump) x = 0 := by
  have h : fderiv ℝ roundBump =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with x' hx'
    exact round_spaceDeriv_far hx'
  rw [h.fderiv_eq]
  exact fderiv_const_apply 0

theorem round_spaceDeriv_near {x : Space} (hx : ‖x‖ < 1) : fderiv ℝ roundBump x = 0 := by
  refine eq_zero_of_eventually (c := 1) ?_
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with x' hx'
  exact roundBump_eq_one (le_of_lt hx')

theorem round_two : ContDiff ℝ 2 roundBump := contDiff_infty.1 roundBump_contDiff 2

theorem round_bounds : ∃ c, 0 ≤ c ∧ ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c ∧ ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c := by
  obtain ⟨c1, h1⟩ := (round_two.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (roundBump_hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨c2, h2⟩ := ((round_two.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    ((roundBump_hasCompactSupport.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  refine ⟨max (max c1 c2) 0, le_max_right _ _, fun x => ⟨?_, ?_⟩⟩
  · exact (h1 x).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h2 x).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem cut_hasSpaceDeriv (R : ℝ) (y : Space) :
    HasFDerivAt (scaledBump R) (R⁻¹ • fderiv ℝ roundBump (R⁻¹ • y)) y := by
  have h1 := ((round_two.differentiable (by norm_num)) (R⁻¹ • y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_smul R⁻¹)
  have h2 : HasFDerivAt (scaledBump R)
      ((fderiv ℝ roundBump (R⁻¹ • y)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Space)) y := h1
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp

theorem cut_spaceDeriv (R : ℝ) : fderiv ℝ (scaledBump R) = fun y => R⁻¹ • fderiv ℝ roundBump (R⁻¹ • y) :=
  funext fun y => (cut_hasSpaceDeriv R y).fderiv

theorem cut_spaceDeriv2 (R : ℝ) (y : Space) :
    fderiv ℝ (fderiv ℝ (scaledBump R)) y = (R⁻¹ * R⁻¹) • fderiv ℝ (fderiv ℝ roundBump) (R⁻¹ • y) := by
  rw [cut_spaceDeriv]
  have hd : Differentiable ℝ (fderiv ℝ roundBump) :=
    (round_two.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 := ((hd (R⁻¹ • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul R⁻¹)).const_smul R⁻¹
  have h2 : HasFDerivAt (fun y => R⁻¹ • fderiv ℝ roundBump (R⁻¹ • y))
      (R⁻¹ • (fderiv ℝ (fderiv ℝ roundBump) (R⁻¹ • y)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Space)) y := h1
  refine h2.fderiv.trans (ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_)
  simp [smul_smul]

theorem cut_two (R : ℝ) : ContDiff ℝ 2 (scaledBump R) := contDiff_infty.1 (scaledBump_contDiff R) 2

theorem smooth_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (h : ContDiff ℝ ∞ f) : ContDiff ℝ 1 f := by
  simpa using contDiff_infty.1 h 1

def trunc (ψ : ℝ → ℝ) (ζ A : ℝ → Space → Space) (R s : ℝ) (y : Space) : Space :=
  ψ s • (scaledBump R y • ζ s y + crossGrad (fderiv ℝ (scaledBump R) y) (A s y))

variable {ψ : ℝ → ℝ} {ζ A : ℝ → Space → Space}

theorem trunc_contDiff (hψ : ContDiff ℝ ∞ ψ) (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2))
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) (R : ℝ) :
    ContDiff ℝ 1 (fun z : ℝ × Space => trunc ψ ζ A R z.1 z.2) := by
  have hψ1 : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1) := (smooth_one hψ).comp contDiff_fst
  have hχ : ContDiff ℝ 1 (fun z : ℝ × Space => scaledBump R z.2) :=
    ((cut_two R).of_le (by norm_num)).comp contDiff_snd
  have hDχ : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (scaledBump R) z.2) :=
    ((cut_two R).fderiv_right (m := 1) (by norm_num)).comp contDiff_snd
  exact hψ1.smul ((hχ.smul hζ).add ((crossGrad.contDiff.comp hDχ).clm_apply hA))

theorem trunc_hasSpaceDeriv (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2))
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) (R s : ℝ) (y : Space) :
    HasFDerivAt (trunc ψ ζ A R s) (ψ s • ((scaledBump R y • fderiv ℝ (ζ s) y
      + (fderiv ℝ (scaledBump R) y).smulRight (ζ s y))
      + (crossGrad.precompR Space (fderiv ℝ (scaledBump R) y) (fderiv ℝ (A s) y)
        + crossGrad.precompL Space (fderiv ℝ (fderiv ℝ (scaledBump R)) y) (A s y)))) y := by
  have hχ : HasFDerivAt (scaledBump R) (fderiv ℝ (scaledBump R) y) y :=
    ((cut_two R).differentiable (by norm_num) y).hasFDerivAt
  have hζ' : HasFDerivAt (ζ s) (fderiv ℝ (ζ s) y) y := (slice_differentiableAt hζ s y).hasFDerivAt
  have hA' : HasFDerivAt (A s) (fderiv ℝ (A s) y) y := (slice_differentiableAt hA s y).hasFDerivAt
  have hDχ : HasFDerivAt (fderiv ℝ (scaledBump R)) (fderiv ℝ (fderiv ℝ (scaledBump R)) y) y :=
    (((cut_two R).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y).hasFDerivAt
  exact ((hχ.smul hζ').add (crossGrad.hasFDerivAt_of_bilinear hDχ hA')).const_smul (ψ s)

theorem trunc_divergence (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2))
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) (hdiv : ∀ σ y, divergenceAt (ζ σ) y = 0)
    (hcurl : ∀ σ y, curlAt (A σ) y = ζ σ y) (R s : ℝ) (y : Space) :
    divergenceAt (trunc ψ ζ A R s) y = 0 := by
  have hsym : IsSymmSndFDerivAt ℝ (scaledBump R) y :=
    (cut_two R).contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hd := hdiv s y
  have c0 := congrArg (fun v : Space => v 0) (hcurl s y)
  have c1 := congrArg (fun v : Space => v 1) (hcurl s y)
  have c2 := congrArg (fun v : Space => v 2) (hcurl s y)
  simp [curlAt, unitVector] at c0 c1 c2
  have s01 := hsym (unitVector 0) (unitVector 1)
  have s02 := hsym (unitVector 0) (unitVector 2)
  have s12 := hsym (unitVector 1) (unitVector 2)
  unfold divergenceAt at hd ⊢
  rw [(trunc_hasSpaceDeriv hζ hA R s y).fderiv]
  simp [Fin.sum_univ_three, crossGrad_comp] at hd ⊢
  simp only [unitVector] at hd s01 s02 s12 ⊢
  linear_combination (ψ s * scaledBump R y) * hd
    - (ψ s * fderiv ℝ (scaledBump R) y (EuclideanSpace.single 0 1)) * c0
    - (ψ s * fderiv ℝ (scaledBump R) y (EuclideanSpace.single 1 1)) * c1
    - (ψ s * fderiv ℝ (scaledBump R) y (EuclideanSpace.single 2 1)) * c2
    + (ψ s * A s y 2) * s01 - (ψ s * A s y 1) * s02 + (ψ s * A s y 0) * s12

theorem cut_abs (R : ℝ) (y : Space) : |scaledBump R y| ≤ 1 := by
  show |roundBump (R⁻¹ • y)| ≤ 1
  rw [abs_of_nonneg (roundBump_nonneg _)]
  exact roundBump_le_one _

theorem norm_inv_smul {R : ℝ} (hR : 0 < R) (y : Space) : ‖R⁻¹ • y‖ = R⁻¹ * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]

theorem cut_spaceDeriv_near {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ < R) : fderiv ℝ (scaledBump R) y = 0 := by
  rw [cut_spaceDeriv]
  show R⁻¹ • fderiv ℝ roundBump (R⁻¹ • y) = 0
  rw [round_spaceDeriv_near, smul_zero]
  rw [norm_inv_smul hR, inv_mul_lt_iff₀ hR]
  linarith

theorem cut_spaceDeriv_far {R : ℝ} (hR : 0 < R) {y : Space} (hy : 2 * R < ‖y‖) : fderiv ℝ (scaledBump R) y = 0 := by
  rw [cut_spaceDeriv]
  show R⁻¹ • fderiv ℝ roundBump (R⁻¹ • y) = 0
  rw [round_spaceDeriv_far, smul_zero]
  rw [norm_inv_smul hR, lt_inv_mul_iff₀ hR]
  linarith

theorem cut_bound1 {R c : ℝ} (hR : 1 ≤ R) (hc0 : 0 ≤ c) (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c) (y : Space) :
    ‖fderiv ℝ (scaledBump R) y‖ ≤ 3 * c / (1 + ‖y‖) ^ (1 : ℝ) := by
  have hR0 : 0 < R := by linarith
  rw [Real.rpow_one, cut_spaceDeriv]
  show ‖R⁻¹ • fderiv ℝ roundBump (R⁻¹ • y)‖ ≤ 3 * c / (1 + ‖y‖)
  by_cases h : 2 < ‖R⁻¹ • y‖
  · rw [round_spaceDeriv_far h, smul_zero, norm_zero]
    positivity
  · replace h := not_lt.1 h
    rw [norm_inv_smul hR0, inv_mul_le_iff₀ hR0] at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0)]
    calc R⁻¹ * ‖fderiv ℝ roundBump (R⁻¹ • y)‖ ≤ R⁻¹ * c :=
          mul_le_mul_of_nonneg_left (hc _) (by positivity)
      _ ≤ 3 * c / (1 + ‖y‖) := by
          rw [inv_mul_eq_div, div_le_div_iff₀ hR0 (by positivity)]
          nlinarith

theorem cut_bound2 {R c : ℝ} (hR : 1 ≤ R) (hc0 : 0 ≤ c) (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c)
    (y : Space) : ‖fderiv ℝ (fderiv ℝ (scaledBump R)) y‖ ≤ 9 * c / (1 + ‖y‖) ^ (2 : ℝ) := by
  have hR0 : 0 < R := by linarith
  rw [Real.rpow_two, cut_spaceDeriv2]
  by_cases h : 2 < ‖R⁻¹ • y‖
  · rw [round_spaceDeriv2_far h, smul_zero, norm_zero]
    positivity
  · replace h := not_lt.1 h
    rw [norm_inv_smul hR0, inv_mul_le_iff₀ hR0] at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc R⁻¹ * R⁻¹ * ‖fderiv ℝ (fderiv ℝ roundBump) (R⁻¹ • y)‖ ≤ R⁻¹ * R⁻¹ * c :=
          mul_le_mul_of_nonneg_left (hc _) (by positivity)
      _ ≤ 9 * c / (1 + ‖y‖) ^ 2 := by
          rw [← mul_inv, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : 1 + ‖y‖ ≤ 3 * R := by linarith
          have h2 : (1 + ‖y‖) ^ 2 ≤ (3 * R) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
          nlinarith

theorem trunc_near {R : ℝ} (hR : 0 < R) (s : ℝ) {y : Space} (hy : ‖y‖ < R) :
    trunc ψ ζ A R s =ᶠ[𝓝 y] timeCutoff ψ ζ s := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with y' hy'
  unfold trunc timeCutoff
  rw [scaledBump_eq_one hR hy'.le, cut_spaceDeriv_near hR hy']
  simp

theorem trunc_far {R : ℝ} (hR : 0 < R) (s : ℝ) {y : Space} (hy : 2 * R < ‖y‖) : trunc ψ ζ A R s y = 0 := by
  unfold trunc
  rw [scaledBump_eq_zero hR hy.le, cut_spaceDeriv_far hR hy]
  simp

theorem trunc_far_spaceDeriv {R : ℝ} (hR : 0 < R) (s : ℝ) {y : Space} (hy : 2 * R < ‖y‖) :
    fderiv ℝ (trunc ψ ζ A R s) y = 0 := by
  have h : trunc ψ ζ A R s =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with y' hy'
    exact trunc_far hR s hy'
  rw [h.fderiv_eq]
  exact fderiv_const_apply 0

theorem core_bound {C c β γ p χ : ℝ} {a b : Space} {L : Space →L[ℝ] ℝ} (y : Space) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hpγ : p ≤ γ) (hpβ : p ≤ β + 1) (hχ : |χ| ≤ 1) (ha : ‖a‖ ≤ C / (1 + ‖y‖) ^ γ)
    (hb : ‖b‖ ≤ C / (1 + ‖y‖) ^ β) (hL : ‖L‖ ≤ 3 * c / (1 + ‖y‖) ^ (1 : ℝ)) :
    ‖χ • a + crossGrad L b‖ ≤ (C + ‖crossGrad‖ * (3 * c) * C) / (1 + ‖y‖) ^ p := by
  have ht : 1 ≤ 1 + ‖y‖ := by have := norm_nonneg y; linarith
  have ht0 : 0 < 1 + ‖y‖ := by linarith
  have hB := norm_nonneg crossGrad
  calc ‖χ • a + crossGrad L b‖ ≤ |χ| * ‖a‖ + ‖crossGrad‖ * ‖L‖ * ‖b‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ (crossGrad.le_opNorm₂ L b))
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * (C / (1 + ‖y‖) ^ γ) + ‖crossGrad‖ * (3 * c / (1 + ‖y‖) ^ (1 : ℝ)) * (C / (1 + ‖y‖) ^ β) := by
        gcongr
    _ = C / (1 + ‖y‖) ^ γ + (‖crossGrad‖ * (3 * c) * C) / (1 + ‖y‖) ^ ((1 : ℝ) + β) := by
        rw [one_mul, mul_assoc, frac_mul ht0, ← mul_div_assoc]
        ring
    _ ≤ C / (1 + ‖y‖) ^ p + (‖crossGrad‖ * (3 * c) * C) / (1 + ‖y‖) ^ p := by
        gcongr ?_ + ?_
        · exact frac_antitone hC ht hpγ
        · exact frac_antitone (by positivity) ht (by linarith)
    _ = (C + ‖crossGrad‖ * (3 * c) * C) / (1 + ‖y‖) ^ p := by rw [add_div]

theorem grad_core_bound {C c β γ p χ : ℝ} {a b : Space} {Da Db : Space →L[ℝ] Space} {L : Space →L[ℝ] ℝ}
    {L2 : Space →L[ℝ] Space →L[ℝ] ℝ} (y : Space) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hpγ : p ≤ γ) (hpβ : p ≤ β + 1) (hχ : |χ| ≤ 1) (ha : ‖a‖ ≤ C / (1 + ‖y‖) ^ γ)
    (hDa : ‖Da‖ ≤ C / (1 + ‖y‖) ^ (γ + 1)) (hb : ‖b‖ ≤ C / (1 + ‖y‖) ^ β)
    (hDb : ‖Db‖ ≤ C / (1 + ‖y‖) ^ (β + 1)) (hL : ‖L‖ ≤ 3 * c / (1 + ‖y‖) ^ (1 : ℝ))
    (hL2 : ‖L2‖ ≤ 9 * c / (1 + ‖y‖) ^ (2 : ℝ)) :
    ‖(χ • Da + L.smulRight a) + (crossGrad.precompR Space L Db + crossGrad.precompL Space L2 b)‖ ≤
      (C + 3 * c * C + ‖crossGrad‖ * (3 * c) * C + ‖crossGrad‖ * (9 * c) * C) / (1 + ‖y‖) ^ (p + 1) := by
  have ht : 1 ≤ 1 + ‖y‖ := by have := norm_nonneg y; linarith
  have ht0 : 0 < 1 + ‖y‖ := by linarith
  have hB := norm_nonneg crossGrad
  have hR : ‖crossGrad.precompR Space L Db‖ ≤ ‖crossGrad‖ * ‖L‖ * ‖Db‖ :=
    ((crossGrad.precompR Space).le_opNorm₂ L Db).trans (by
      gcongr
      exact ContinuousLinearMap.norm_precompR_le Space crossGrad)
  have hL' : ‖crossGrad.precompL Space L2 b‖ ≤ ‖crossGrad‖ * ‖L2‖ * ‖b‖ :=
    ((crossGrad.precompL Space).le_opNorm₂ L2 b).trans (by
      gcongr
      exact ContinuousLinearMap.norm_precompL_le Space crossGrad)
  have e1 : 3 * c / (1 + ‖y‖) ^ (1 : ℝ) * (C / (1 + ‖y‖) ^ γ) = 3 * c * C / (1 + ‖y‖) ^ ((1 : ℝ) + γ) :=
    frac_mul ht0
  have e2 : ‖crossGrad‖ * (3 * c / (1 + ‖y‖) ^ (1 : ℝ)) * (C / (1 + ‖y‖) ^ (β + 1)) =
      ‖crossGrad‖ * (3 * c) * C / (1 + ‖y‖) ^ ((1 : ℝ) + (β + 1)) := by
    rw [mul_assoc, frac_mul ht0]
    ring
  have e3 : ‖crossGrad‖ * (9 * c / (1 + ‖y‖) ^ (2 : ℝ)) * (C / (1 + ‖y‖) ^ β) =
      ‖crossGrad‖ * (9 * c) * C / (1 + ‖y‖) ^ ((2 : ℝ) + β) := by
    rw [mul_assoc, frac_mul ht0]
    ring
  calc _ ≤ |χ| * ‖Da‖ + ‖L‖ * ‖a‖ + (‖crossGrad‖ * ‖L‖ * ‖Db‖ + ‖crossGrad‖ * ‖L2‖ * ‖b‖) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_))
          ((norm_add_le _ _).trans (add_le_add hR hL')))
        · rw [norm_smul, Real.norm_eq_abs]
        · rw [ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ 1 * (C / (1 + ‖y‖) ^ (γ + 1)) + 3 * c / (1 + ‖y‖) ^ (1 : ℝ) * (C / (1 + ‖y‖) ^ γ)
        + (‖crossGrad‖ * (3 * c / (1 + ‖y‖) ^ (1 : ℝ)) * (C / (1 + ‖y‖) ^ (β + 1))
          + ‖crossGrad‖ * (9 * c / (1 + ‖y‖) ^ (2 : ℝ)) * (C / (1 + ‖y‖) ^ β)) := by
        gcongr
    _ = C / (1 + ‖y‖) ^ (γ + 1) + 3 * c * C / (1 + ‖y‖) ^ ((1 : ℝ) + γ)
        + (‖crossGrad‖ * (3 * c) * C / (1 + ‖y‖) ^ ((1 : ℝ) + (β + 1))
          + ‖crossGrad‖ * (9 * c) * C / (1 + ‖y‖) ^ ((2 : ℝ) + β)) := by
        rw [one_mul, e1, e2, e3]
    _ ≤ C / (1 + ‖y‖) ^ (p + 1) + 3 * c * C / (1 + ‖y‖) ^ (p + 1)
        + (‖crossGrad‖ * (3 * c) * C / (1 + ‖y‖) ^ (p + 1)
          + ‖crossGrad‖ * (9 * c) * C / (1 + ‖y‖) ^ (p + 1)) := by
        gcongr ?_ + ?_ + (?_ + ?_)
        · exact frac_antitone hC ht (by linarith)
        · exact frac_antitone (by positivity) ht (by linarith)
        · exact frac_antitone (by positivity) ht (by linarith)
        · exact frac_antitone (by positivity) ht (by linarith)
    _ = _ := by ring

theorem field_C_nonneg {C γ : ℝ} (hζ : IsAdjointField ζ C γ) : 0 ≤ C := by
  have h := (hζ.decay 0 0).1
  rw [norm_zero, add_zero, Real.one_rpow, div_one] at h
  exact (norm_nonneg _).trans h

theorem trunc_bound {C c β γ p R : ℝ} (hζ : IsAdjointField ζ C γ) (hA : IsCurlPotential ζ A C β)
    (hc0 : 0 ≤ c) (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c) (hR : 1 ≤ R) (hpγ : p ≤ γ) (hpβ : p ≤ β + 1)
    (s : ℝ) (y : Space) :
    ‖trunc ψ ζ A R s y‖ ≤ |ψ s| * ((C + ‖crossGrad‖ * (3 * c) * C) / (1 + ‖y‖) ^ p) := by
  unfold trunc
  rw [norm_smul, Real.norm_eq_abs]
  gcongr
  exact core_bound y (field_C_nonneg hζ) hc0 hpγ hpβ (cut_abs R y) (hζ.decay s y).1 (hA.decay s y).1
    (cut_bound1 hR hc0 hc y)

theorem trunc_grad_bound {C c β γ p R : ℝ} (hζ : IsAdjointField ζ C γ) (hA : IsCurlPotential ζ A C β)
    (hc0 : 0 ≤ c) (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c ∧ ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c)
    (hR : 1 ≤ R) (hpγ : p ≤ γ) (hpβ : p ≤ β + 1) (s : ℝ) (y : Space) :
    ‖fderiv ℝ (trunc ψ ζ A R s) y‖ ≤ |ψ s| * ((C + 3 * c * C + ‖crossGrad‖ * (3 * c) * C
      + ‖crossGrad‖ * (9 * c) * C) / (1 + ‖y‖) ^ (p + 1)) := by
  rw [(trunc_hasSpaceDeriv hζ.smooth hA.smooth R s y).fderiv, norm_smul, Real.norm_eq_abs]
  gcongr
  exact grad_core_bound y (field_C_nonneg hζ) hc0 hpγ hpβ (cut_abs R y) (hζ.decay s y).1 (hζ.decay s y).2.2
    (hA.decay s y).1 (hA.decay s y).2.2 (cut_bound1 hR hc0 (fun x => (hc x).1) y)
    (cut_bound2 hR hc0 (fun x => (hc x).2) y)

theorem trunc_time_hasDerivAt (hψ : ContDiff ℝ ∞ ψ) (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2))
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) (R s : ℝ) (y : Space) :
    HasDerivAt (fun s' => trunc ψ ζ A R s' y)
      (ψ s • (scaledBump R y • timeDerivative ζ s y + crossGrad (fderiv ℝ (scaledBump R) y) (timeDerivative A s y))
        + deriv ψ s • (scaledBump R y • ζ s y + crossGrad (fderiv ℝ (scaledBump R) y) (A s y))) s := by
  have hψd : HasDerivAt ψ (deriv ψ s) s := ((smooth_one hψ).differentiable one_ne_zero s).hasDerivAt
  have h1 := ((time_hasDerivAt' hζ s y).const_smul (scaledBump R y)).add
    ((crossGrad (fderiv ℝ (scaledBump R) y)).hasFDerivAt.comp_hasDerivAt s (time_hasDerivAt' hA s y))
  exact hψd.smul h1

theorem trunc_time_bound {C c β γ p R : ℝ} (hψ : ContDiff ℝ ∞ ψ) (hζ : IsAdjointField ζ C γ)
    (hA : IsCurlPotential ζ A C β) (hc0 : 0 ≤ c) (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c) (hR : 1 ≤ R)
    (hpγ : p ≤ γ) (hpβ : p ≤ β + 1) (s : ℝ) (y : Space) :
    ‖timeDerivative (trunc ψ ζ A R) s y‖ ≤
      (|ψ s| + |deriv ψ s|) * ((C + ‖crossGrad‖ * (3 * c) * C) / (1 + ‖y‖) ^ p) := by
  unfold timeDerivative
  rw [(trunc_time_hasDerivAt hψ hζ.smooth hA.smooth R s y).deriv, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact core_bound y (field_C_nonneg hζ) hc0 hpγ hpβ (cut_abs R y) (hζ.decay s y).2.1 (hA.decay s y).2.1
      (cut_bound1 hR hc0 hc y)
  · rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact core_bound y (field_C_nonneg hζ) hc0 hpγ hpβ (cut_abs R y) (hζ.decay s y).1 (hA.decay s y).1
      (cut_bound1 hR hc0 hc y)

end Internal.TestDensity

end AdjointDefect

end Breakdown
