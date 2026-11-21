import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

open scoped FourierTransform

namespace Internal.BilinCompact

theorem lpProd_six_three : ENNReal.HolderTriple 6 3 2 := by
  constructor
  have h6 : (6 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/6) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have h3 : (3 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/3) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h6, h3, h2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem phiFactor_nonneg (τ : ℝ) (ξ : Space) : 0 ≤ phiFactor τ ξ := by
  unfold phiFactor; positivity

theorem phiFactor_tail {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R) {ξ : Space} (hξ : R ≤ ‖ξ‖) :
    phiFactor τ ξ ≤ 1 / (2 * π * τ * R) := by
  unfold phiFactor
  set r := ‖ξ‖ with hr
  have hr0 : 0 < r := lt_of_lt_of_le hR hξ
  have hE := Real.add_one_le_exp (4 * π ^ 2 * τ * r ^ 2)
  have hpos : 0 < Real.exp (4 * π ^ 2 * τ * r ^ 2) := Real.exp_pos _
  rw [Real.exp_neg, le_div_iff₀ (by positivity)]
  have key : 4 * π ^ 2 * τ * r * R ≤ Real.exp (4 * π ^ 2 * τ * r ^ 2) := by
    have : 4 * π ^ 2 * τ * r * R ≤ 4 * π ^ 2 * τ * r ^ 2 := by
      have h1 : 0 ≤ 4 * π ^ 2 * τ * r := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hξ h1]
    linarith
  calc 2 * π * r * (Real.exp (4 * π ^ 2 * τ * r ^ 2))⁻¹ * (2 * π * τ * R)
      = (4 * π ^ 2 * τ * r * R) * (Real.exp (4 * π ^ 2 * τ * r ^ 2))⁻¹ := by ring
    _ ≤ Real.exp (4 * π ^ 2 * τ * r ^ 2) * (Real.exp (4 * π ^ 2 * τ * r ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = 1 := mul_inv_cancel₀ hpos.ne'

theorem phiFactor_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) : phiFactor τ ξ ≤ 2 * π + 1 / (2 * π * τ) := by
  rcases le_or_gt 1 ‖ξ‖ with h | h
  · have := phiFactor_tail hτ one_pos h
    rw [mul_one] at this
    linarith [Real.pi_pos]
  · unfold phiFactor
    have h1 : Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : 0 ≤ 4 * π ^ 2 * τ * ‖ξ‖ ^ 2 := by positivity
      linarith
    have h2 : 0 < 1 / (2 * π * τ) := by positivity
    have h3 : 2 * π * ‖ξ‖ ≤ 2 * π := by
      have := norm_nonneg ξ; nlinarith [Real.pi_pos]
    calc 2 * π * ‖ξ‖ * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2)) ≤ 2 * π * ‖ξ‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * π + 1 / (2 * π * τ) := by linarith

theorem continuous_phiFactor (τ : ℝ) : Continuous (phiFactor τ) := by
  unfold phiFactor; fun_prop

def phiMul (τ : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace)

theorem phiMul_ae (h4 : FieldOpRealized) {τ : ℝ} (hτ : 0 < τ) (u : L2C) :
    (phiMul τ u : Space → CSpace) =ᵐ[volume] fun ξ => phiFactor τ ξ • (u : Space → CSpace) ξ := by
  have hmeas : AEStronglyMeasurable (fun ξ : Space => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    ((continuous_phiFactor τ).smul continuous_const).aestronglyMeasurable
  have hb : ∀ ξ, ‖phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 2 * π + 1 / (2 * π * τ) := by
    intro ξ
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (phiFactor_nonneg τ ξ)]
    calc phiFactor τ ξ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ phiFactor τ ξ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (phiFactor_nonneg τ ξ)
      _ ≤ _ := by rw [mul_one]; exact phiFactor_le hτ ξ
  have := h4 (ContinuousLinearEquiv.refl ℝ Space) _ _ hmeas hb u
  exact this

theorem norm_complexifyVec (z : Space) : ‖complexifyVec z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [complexifyVec]

theorem eChar_sub_le (a b : ℝ) : ‖(Real.fourierChar a : ℂ) - Real.fourierChar b‖ ≤ 2 * π * |a - b| := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply]
  have h1 : Complex.exp (↑(2 * π * a) * Complex.I) - Complex.exp (↑(2 * π * b) * Complex.I) =
      Complex.exp (↑(2 * π * b) * Complex.I) * (Complex.exp (Complex.I * ↑(2 * π * (a - b))) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast; ring
  rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]

theorem norm_freqTr_le (G : Space → CSpace) (ξ : Space) : ‖𝓕 G ξ‖ ≤ ∫ x, ‖G x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem continuous_freqTr_of_integrable {G : Space → CSpace} (hG : Integrable G) : Continuous (𝓕 G) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by exact continuous_inner) hG

theorem freqTr_sub_le {G : Space → CSpace} (hG : Integrable G) {ρ : ℝ}
    (hsupp : ∀ x, G x ≠ 0 → ‖x‖ ≤ ρ) (ξ η : Space) :
    ‖𝓕 G ξ - 𝓕 G η‖ ≤ 2 * π * ρ * ‖ξ - η‖ * ∫ x, ‖G x‖ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_sub]
  rotate_left
  · exact (Real.fourierIntegral_convergent_iff ξ).2 hG
  · exact (Real.fourierIntegral_convergent_iff η).2 hG
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hG.norm.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
  rw [Circle.smul_def, Circle.smul_def, ← sub_smul, norm_smul]
  by_cases hx : G x = 0
  · simp [hx]
  have hxρ := hsupp x hx
  have hρ : 0 ≤ ρ := (norm_nonneg x).trans hxρ
  refine (mul_le_mul_of_nonneg_right (eChar_sub_le _ _) (norm_nonneg _)).trans ?_
  have hab : |-inner ℝ x ξ - -inner ℝ x η| ≤ ρ * ‖ξ - η‖ := by
    rw [show -inner ℝ x ξ - -inner ℝ x η = -inner ℝ x (ξ - η) by rw [inner_sub_right]; ring, abs_neg]
    exact (abs_real_inner_le_norm x _).trans (mul_le_mul_of_nonneg_right hxρ (norm_nonneg _))
  calc 2 * π * |-inner ℝ x ξ - -inner ℝ x η| * ‖G x‖ ≤ 2 * π * (ρ * ‖ξ - η‖) * ‖G x‖ := by
        gcongr
    _ = 2 * π * ρ * ‖ξ - η‖ * ‖G x‖ := by ring

end Internal.BilinCompact


namespace Internal.BilinCompact

def cutField (K : Set Space) (g : L2R) : Space → CSpace :=
  K.indicator (fun x => complexifyVec ((g : Space → Space) x))

def supSet (K : Set Space) (C : ℝ) : Set L2R :=
  {g | ‖g‖ ≤ C ∧ ∀ᵐ x ∂volume, x ∉ K → (g : Space → Space) x = 0}

theorem memLp_complexify (g : L2R) : MemLp (fun x => complexifyVec ((g : Space → Space) x)) 2 volume :=
  complexifyVec.comp_memLp' (Lp.memLp g)

theorem memLp_cutField {K : Set Space} (hK : IsCompact K) (g : L2R) : MemLp (cutField K g) 2 volume :=
  (memLp_complexify g).indicator hK.measurableSet

theorem integrable_cutField {K : Set Space} (hK : IsCompact K) (g : L2R) : Integrable (cutField K g) := by
  unfold cutField
  rw [integrable_indicator_iff hK.measurableSet]
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact ((memLp_complexify g).restrict K).integrable (by norm_num)

theorem integral_sq_norm (g : L2R) : ∫ x, ‖(g : Space → Space) x‖ ^ 2 = ‖g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  exact (real_inner_self_eq_norm_sq _).symm

theorem integral_norm_cutField_le {K : Set Space} (hK : IsCompact K) (g : L2R) :
    ∫ x, ‖cutField K g x‖ ≤ volume.real K * (1 / 2) + ‖g‖ ^ 2 / 2 := by
  have hsq : Integrable (fun x => ‖(g : Space → Space) x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have hind : Integrable (K.indicator (fun _ => (1 / 2 : ℝ))) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hpt : ∀ x, ‖cutField K g x‖ ≤
      K.indicator (fun _ => (1 / 2 : ℝ)) x + ‖(g : Space → Space) x‖ ^ 2 / 2 := by
    intro x
    unfold cutField
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, indicator_of_mem hx, norm_complexifyVec]
      nlinarith [sq_nonneg (‖(g : Space → Space) x‖ - 1)]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, norm_zero]; positivity
  calc ∫ x, ‖cutField K g x‖
      ≤ ∫ x, (K.indicator (fun _ => (1 / 2 : ℝ)) x + ‖(g : Space → Space) x‖ ^ 2 / 2) :=
        integral_mono (integrable_cutField hK g).norm (hind.add (hsq.div_const 2)) hpt
    _ = volume.real K * (1 / 2) + ‖g‖ ^ 2 / 2 := by
        rw [integral_add hind (hsq.div_const 2), integral_indicator_const _ hK.measurableSet,
          integral_div, integral_sq_norm, smul_eq_mul]

theorem complexify_eq_toLp {K : Set Space} (hK : IsCompact K) {g : L2R}
    (hg : ∀ᵐ x ∂volume, x ∉ K → (g : Space → Space) x = 0) :
    complexify g = toLpOrZero 2 (cutField K g) := by
  have hm := memLp_cutField hK g
  rw [toLpOrZero, dif_pos hm]
  have h1 : (complexify g : Space → CSpace) =ᵐ[volume] fun x => complexifyVec ((g : Space → Space) x) :=
    ContinuousLinearMap.coeFn_compLp complexifyVec g
  apply Lp.ext
  filter_upwards [h1, hm.coeFn_toLp, hg] with x h1 h2 h3
  rw [h1, h2]
  unfold cutField
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, h3 hx, map_zero]

theorem freqTrR_complexify_ae (h2 : FreqTrL1L2) {K : Set Space} (hK : IsCompact K) {g : L2R}
    (hg : ∀ᵐ x ∂volume, x ∉ K → (g : Space → Space) x = 0) :
    (freqTrR (complexify g) : Space → CSpace) =ᵐ[volume] 𝓕 (cutField K g) := by
  rw [complexify_eq_toLp hK hg]
  exact h2 _ (memLp_one_iff_integrable.2 (integrable_cutField hK g)) (memLp_cutField hK g)

end Internal.BilinCompact


namespace Internal.BilinCompact

open scoped BoundedContinuousFunction Classical

abbrev ballR (R : ℝ) : Set Space := Metric.closedBall (0 : Space) R

def extendField (τ R : ℝ) (f : ballR R →ᵇ CSpace) : Space → CSpace :=
  fun ξ => if h : ξ ∈ ballR R then phiFactor τ ξ • f ⟨ξ, h⟩ else 0

theorem extendField_eq (τ R : ℝ) (f : ballR R →ᵇ CSpace) :
    extendField τ R f = (ballR R).indicator (extendField τ R f) := by
  funext ξ
  by_cases h : ξ ∈ ballR R
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]; simp [extendField, h]

theorem continuousOn_extendField (τ R : ℝ) (f : ballR R →ᵇ CSpace) :
    ContinuousOn (extendField τ R f) (ballR R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (ballR R).domRestrict (extendField τ R f) = fun x : ballR R => phiFactor τ x • f x := by
    funext x; simp [extendField, x.2]
  rw [this]
  exact ((continuous_phiFactor τ).comp continuous_subtype_val).smul f.continuous

theorem norm_extendField_le {τ R : ℝ} (hτ : 0 < τ) (f : ballR R →ᵇ CSpace) (ξ : Space) :
    ‖extendField τ R f ξ‖ ≤ (2 * π + 1 / (2 * π * τ)) * ‖f‖ := by
  unfold extendField
  split_ifs with h
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (phiFactor_nonneg _ _)]
    exact mul_le_mul (phiFactor_le hτ ξ) (f.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
  · rw [norm_zero]; positivity

theorem memLp_extendField {τ R : ℝ} (hτ : 0 < τ) (f : ballR R →ᵇ CSpace) :
    MemLp (extendField τ R f) 2 volume := by
  rw [extendField_eq, memLp_indicator_iff_restrict measurableSet_closedBall]
  have : IsFiniteMeasure (volume.restrict (ballR R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  exact MemLp.of_bound ((continuousOn_extendField τ R f).aestronglyMeasurable measurableSet_closedBall) _
    (Filter.Eventually.of_forall (norm_extendField_le hτ f))

def cutLp (τ R : ℝ) (f : ballR R →ᵇ CSpace) : L2C := toLpOrZero 2 (extendField τ R f)

theorem cutLp_ae {τ R : ℝ} (hτ : 0 < τ) (f : ballR R →ᵇ CSpace) :
    (cutLp τ R f : Space → CSpace) =ᵐ[volume] extendField τ R f := by
  unfold cutLp toLpOrZero
  rw [dif_pos (memLp_extendField hτ f)]
  exact (memLp_extendField hτ f).coeFn_toLp

theorem dist_cutLp_le {τ R : ℝ} (hτ : 0 < τ) :
    ∃ c : ℝ, ∀ f f' : ballR R →ᵇ CSpace, dist (cutLp τ R f) (cutLp τ R f') ≤ c * dist f f' := by
  have hχ : MemLp ((ballR R).indicator (fun _ => (1 : ℝ))) 2 volume :=
    memLp_indicator_const 2 measurableSet_closedBall (1 : ℝ) (Or.inr measure_closedBall_lt_top.ne)
  refine ⟨(2 * π + 1 / (2 * π * τ)) * ‖hχ.toLp _‖, fun f f' => ?_⟩
  rw [dist_eq_norm]
  have key : ‖cutLp τ R f - cutLp τ R f'‖ ≤ ((2 * π + 1 / (2 * π * τ)) * dist f f') * ‖hχ.toLp _‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (cutLp τ R f) (cutLp τ R f'), cutLp_ae hτ f, cutLp_ae hτ f',
      hχ.coeFn_toLp] with ξ h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4]
    by_cases h : ξ ∈ ballR R
    · rw [indicator_of_mem h, norm_one, mul_one]
      simp only [extendField, dif_pos h]
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (phiFactor_nonneg _ _)]
      have hd : ‖f ⟨ξ, h⟩ - f' ⟨ξ, h⟩‖ ≤ dist f f' := by
        rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist _
      exact mul_le_mul (phiFactor_le hτ ξ) hd (norm_nonneg _) (by positivity)
    · simp only [extendField, dif_neg h, indicator_of_notMem h, sub_zero, norm_zero, mul_zero, le_refl]
  exact key.trans (le_of_eq (by ring))

def fcut {K : Set Space} (hK : IsCompact K) (R : ℝ) (g : L2R) : ballR R →ᵇ CSpace :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun ξ => 𝓕 (cutField K g) ξ,
      (continuous_freqTr_of_integrable (integrable_cutField hK g)).comp continuous_subtype_val⟩

theorem fcut_apply {K : Set Space} (hK : IsCompact K) (R : ℝ) (g : L2R) (ξ : ballR R) :
    fcut hK R g ξ = 𝓕 (cutField K g) ξ := rfl

theorem tail_le (h2 : FreqTrL1L2) (h4 : FieldOpRealized) {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R)
    {K : Set Space} (hK : IsCompact K) {g : L2R}
    (hg : ∀ᵐ x ∂volume, x ∉ K → (g : Space → Space) x = 0) :
    ‖phiMul τ (freqTrR (complexify g)) - cutLp τ R (fcut hK R g)‖ ≤
      1 / (2 * π * τ * R) * ‖freqTrR (complexify g)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (phiMul τ (freqTrR (complexify g))) (cutLp τ R (fcut hK R g)),
    phiMul_ae h4 hτ (freqTrR (complexify g)), cutLp_ae hτ (fcut hK R g),
    freqTrR_complexify_ae h2 hK hg] with ξ h1 h3 h5 h6
  rw [h1, Pi.sub_apply, h3, h5]
  by_cases h : ξ ∈ ballR R
  · simp only [extendField, dif_pos h]
    rw [fcut_apply, ← h6, sub_self, norm_zero]
    positivity
  · simp only [extendField, dif_neg h, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (phiFactor_nonneg _ _)]
    have hξ : R ≤ ‖ξ‖ := by
      simp only [ballR, Metric.mem_closedBall, dist_zero_right, not_le] at h
      exact h.le
    exact mul_le_mul_of_nonneg_right (phiFactor_tail hτ hR hξ) (norm_nonneg _)

theorem isCompact_closure_fcut {K : Set Space} (hK : IsCompact K) (R C : ℝ) :
    IsCompact (closure (fcut hK R '' supSet K C)) := by
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall (0 : Space)
  have hN : ∀ g ∈ supSet K C, ∫ x, ‖cutField K g x‖ ≤ volume.real K * (1 / 2) + C ^ 2 / 2 := by
    intro g hg
    refine (integral_norm_cutField_le hK g).trans ?_
    have : ‖g‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg.1 2
    linarith
  have hsupp : ∀ g : L2R, ∀ x, cutField K g x ≠ 0 → ‖x‖ ≤ max ρ 0 := by
    intro g x hx
    have hxK : x ∈ K := by
      by_contra hn
      exact hx (by simp [cutField, indicator_of_notMem hn])
    have := hρ hxK
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  apply BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : CSpace) (volume.real K * (1 / 2) + C ^ 2 / 2)) (isCompact_closedBall _ _)
  · rintro f ξ ⟨g, hg, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, fcut_apply]
    exact (norm_freqTr_le _ _).trans (hN g hg)
  · refine (LipschitzWith.uniformEquicontinuous _
      (Real.toNNReal (2 * π * max ρ 0 * (volume.real K * (1 / 2) + C ^ 2 / 2))) ?_).equicontinuous
    rintro ⟨f, g, hg, rfl⟩
    apply LipschitzWith.of_dist_le'
    intro ξ η
    rw [dist_eq_norm, fcut_apply, fcut_apply, Subtype.dist_eq, dist_eq_norm]
    refine (freqTr_sub_le (integrable_cutField hK g) (hsupp g) ξ η).trans ?_
    have h0 : 0 ≤ 2 * π * max ρ 0 * ‖(ξ : Space) - η‖ := by positivity
    calc 2 * π * max ρ 0 * ‖(ξ : Space) - η‖ * ∫ x, ‖cutField K g x‖
        ≤ 2 * π * max ρ 0 * ‖(ξ : Space) - η‖ * (volume.real K * (1 / 2) + C ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (hN g hg) h0
      _ = 2 * π * max ρ 0 * (volume.real K * (1 / 2) + C ^ 2 / 2) * ‖(ξ : Space) - η‖ := by ring

end Internal.BilinCompact


namespace Internal.BilinCompact

theorem totallyBounded_image (h2 : FreqTrL1L2) (h4 : FieldOpRealized) {τ : ℝ} (hτ : 0 < τ)
    {K : Set Space} (hK : IsCompact K) {C : ℝ} (hC : 0 ≤ C) :
    TotallyBounded ((fun g : L2R => phiMul τ (freqTrR (complexify g))) '' supSet K C) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hD : 0 ≤ ‖complexify‖ * C := by positivity
  have ha : 0 < 2 * π * τ := by positivity
  obtain ⟨R, hR, htail⟩ : ∃ R : ℝ, 0 < R ∧ 1 / (2 * π * τ * R) * (‖complexify‖ * C) < ε / 2 := by
    refine ⟨4 * (‖complexify‖ * C) / (2 * π * τ * ε) + 1, by positivity, ?_⟩
    have hRe : 2 * π * τ * (4 * (‖complexify‖ * C) / (2 * π * τ * ε) + 1) * ε =
        4 * (‖complexify‖ * C) + 2 * π * τ * ε := by
      field_simp
    rw [one_div, inv_mul_eq_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos ha hε]
  obtain ⟨c, hc⟩ := dist_cutLp_le (R := R) hτ
  have hcomp : IsCompact (cutLp τ R '' closure (fcut hK R '' supSet K C)) :=
    (isCompact_closure_fcut hK R C).image (LipschitzWith.of_dist_le' hc).continuous
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 hcomp.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  have hm : cutLp τ R (fcut hK R g) ∈ cutLp τ R '' closure (fcut hK R '' supSet K C) :=
    ⟨_, subset_closure ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨y, hy, hdist⟩ := mem_iUnion₂.1 (hcov hm)
  refine mem_iUnion₂.2 ⟨y, hy, ?_⟩
  rw [Metric.mem_ball] at hdist ⊢
  have hu : ‖freqTrR (complexify g)‖ ≤ ‖complexify‖ * C := by
    have : ‖freqTrR (complexify g)‖ = ‖complexify g‖ := freqTrL2.norm_map (complexify g)
    rw [this]
    exact (complexify.le_opNorm g).trans (mul_le_mul_of_nonneg_left hg.1 (norm_nonneg _))
  have ht' := tail_le h2 h4 hτ hR hK hg.2
  have hfirst : dist (phiMul τ (freqTrR (complexify g))) (cutLp τ R (fcut hK R g)) < ε / 2 := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (ht'.trans (mul_le_mul_of_nonneg_left hu (by positivity))) htail
  calc dist (phiMul τ (freqTrR (complexify g))) y
      ≤ dist (phiMul τ (freqTrR (complexify g))) (cutLp τ R (fcut hK R g)) +
        dist (cutLp τ R (fcut hK R g)) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hdist
    _ = ε := by ring

def advectTerm (φ : Space → Space) (v : X) (j : Fin 3) : Space → Space :=
  fun x => φ x j • (partialX j v : Space → Space) x + (velocity v : Space → Space) x j • partialField φ j x

theorem advect_mem {φ : Space → Space} (hφ : IsTestField φ) :
    ∃ C, 0 ≤ C ∧ ∀ v : X, ‖v‖ ≤ 1 → advectTest φ v ∈ supSet (tsupport φ) C := by
  have : ENNReal.HolderTriple 6 3 2 := lpProd_six_three
  obtain ⟨A, hA⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  have hpc : ∀ j, Continuous (partialField φ j) := fun j =>
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpz : ∀ j x, x ∉ tsupport φ → partialField φ j x = 0 := by
    intro j x hx
    simp [partialField, fderiv_of_notMem_tsupport ℝ hx]
  have hφz : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hpm : ∀ j, MemLp (partialField φ j) 3 volume := fun j =>
    (hpc j).memLp_of_hasCompactSupport (hφ.2.1.mono' (fun x hx => by
      by_contra hn
      exact hx (hpz j x hn)))
  have hcomp : ∀ (z : Space) (j : Fin 3), ‖z j‖ ≤ ‖z‖ := fun z j => PiLp.norm_apply_le z j
  have hφj : ∀ j : Fin 3, Continuous (fun x => φ x j) := fun j => by
    have := hφ.1.continuous
    fun_prop
  refine ⟨(∑ j : Fin 3, (ENNReal.ofReal A * ENNReal.ofReal ‖partialX j‖ +
      ENNReal.ofReal ‖velocity‖ * eLpNorm (partialField φ j) 3 volume)).toReal,
      ENNReal.toReal_nonneg, fun v hv => ?_⟩
  have hEfin : (∑ j : Fin 3, (ENNReal.ofReal A * ENNReal.ofReal ‖partialX j‖ +
      ENNReal.ofReal ‖velocity‖ * eLpNorm (partialField φ j) 3 volume)) ≠ (⊤ : ℝ≥0∞) := by
    refine (ENNReal.sum_lt_top.2 (fun j _ => ?_)).ne
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hpm j).eLpNorm_lt_top⟩
  have hVm : ∀ j : Fin 3, AEStronglyMeasurable (fun x => (velocity v : Space → Space) x j) volume :=
    fun j => (by fun_prop : Continuous fun z : Space => z j).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _)
  have hsum : (fun x => ∑ j : Fin 3, (φ x j • (partialX j v : Space → Space) x +
      (velocity v : Space → Space) x j • partialField φ j x)) = ∑ j, advectTerm φ v j := by
    funext x
    simp [advectTerm, Finset.sum_apply]
  have ha : ∀ j : Fin 3, ∀ x, ‖φ x j • (partialX j v : Space → Space) x‖ ≤
      A * ‖(partialX j v : Space → Space) x‖ := fun j x => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right ((hcomp _ j).trans (hA x)) (norm_nonneg _)
  have hamem : ∀ j : Fin 3, MemLp (fun x => φ x j • (partialX j v : Space → Space) x) 2 volume :=
    fun j => (Lp.memLp (partialX j v)).of_le_mul
      ((hφj j).aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)) (Filter.Eventually.of_forall (ha j))
  have hVmem : ∀ j : Fin 3, MemLp (fun x => (velocity v : Space → Space) x j) 6 volume := fun j =>
    (Lp.memLp (velocity v)).of_le (hVm j) (Filter.Eventually.of_forall fun x => by
      simpa using hcomp ((velocity v : Space → Space) x) j)
  have hbmem : ∀ j : Fin 3,
      MemLp (fun x => (velocity v : Space → Space) x j • partialField φ j x) 2 volume :=
    fun j => (hpm j).smul (hVmem j)
  have hFmem : ∀ j, MemLp (advectTerm φ v j) 2 volume := fun j => (hamem j).add (hbmem j)
  have hmem : MemLp (fun x => ∑ j : Fin 3, (φ x j • (partialX j v : Space → Space) x +
      (velocity v : Space → Space) x j • partialField φ j x)) 2 volume := by
    rw [hsum]
    exact memLp_finsetSum' _ (fun j _ => hFmem j)
  have hbound : eLpNorm (∑ j, advectTerm φ v j) 2 volume ≤
      ∑ j : Fin 3, (ENNReal.ofReal A * ENNReal.ofReal ‖partialX j‖ +
        ENNReal.ofReal ‖velocity‖ * eLpNorm (partialField φ j) 3 volume) := by
    refine (eLpNorm_sum_le (fun j _ => (hFmem j).aestronglyMeasurable) (by norm_num)).trans ?_
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (eLpNorm_add_le (hamem j).aestronglyMeasurable (hbmem j).aestronglyMeasurable
      (by norm_num)).trans ?_
    gcongr ?_ + ?_
    · refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall (ha j)) 2).trans ?_
      gcongr
      have he : eLpNorm (partialX j v : Space → Space) 2 volume = ENNReal.ofReal ‖partialX j v‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      rw [he]
      exact ENNReal.ofReal_le_ofReal
        (((partialX j).le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv))
    · have hb := eLpNorm_smul_le_mul_eLpNorm (p := 6) (q := 3) (r := 2) (μ := volume)
        (hpm j).aestronglyMeasurable (hVm j)
      refine le_trans hb ?_
      gcongr
      have he : eLpNorm (velocity v : Space → Space) 6 volume = ENNReal.ofReal ‖velocity v‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      refine (eLpNorm_mono (fun x => ?_)).trans (le_of_eq_of_le he ?_)
      · simpa using hcomp ((velocity v : Space → Space) x) j
      · exact ENNReal.ofReal_le_ofReal
          ((velocity.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv))
  refine ⟨?_, ?_⟩
  · unfold advectTest toLpOrZero
    rw [dif_pos hmem, Lp.norm_toLp, hsum]
    exact ENNReal.toReal_mono hEfin hbound
  · unfold advectTest toLpOrZero
    rw [dif_pos hmem]
    filter_upwards [hmem.coeFn_toLp] with x hx hxK
    rw [hx]
    have e1 : φ x = 0 := hφz x hxK
    have e2 : ∀ j, partialField φ j x = 0 := fun j => hpz j x hxK
    simp [e1, e2]

end Internal.BilinCompact

theorem bilinCompact (h1 : BilinTestFormula) (h2 : FreqTrL1L2) (h3 : TestSpanSpec)
    (h4 : FieldOpRealized) (_h5 : VelocityExists) (_h6 : PartialNormLe) (_h7 : EmbedLinear) :
    BilinCompact := by
  intro x hx τ hτ
  obtain ⟨φ, hφ, rfl⟩ := h3 x hx
  have hfun : ⇑(bilinX τ (embedX φ)) = fun v =>
      (-(1 / 2 : ℝ)) • projX (Internal.BilinCompact.phiMul τ (freqTrR (complexify (advectTest φ v)))) := by
    funext v
    rw [h1 φ hφ τ hτ v]
    rfl
  rw [hfun, isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  obtain ⟨C, hC, hmem⟩ := Internal.BilinCompact.advect_mem hφ
  have hK : IsCompact (tsupport φ) := hφ.2.1
  have htb := Internal.BilinCompact.totallyBounded_image h2 h4 hτ hK hC
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos,
    (fun y => (-(1 / 2 : ℝ)) • projX y) ''
      closure ((fun g : L2R => Internal.BilinCompact.phiMul τ (freqTrR (complexify g))) ''
        Internal.BilinCompact.supSet (tsupport φ) C),
    (htb.closure.isCompact_of_isClosed isClosed_closure).image
      (by fun_prop), ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨_, subset_closure ⟨_, hmem v (mem_closedBall_zero_iff.1 hv), rfl⟩, rfl⟩

end Breakdown.Freq
