import Breakdown.FracCert.StFreeNiceParts
import Breakdown.Uniqueness.RegPhysAuxDeriv
import Breakdown.Uniqueness.RegPhysAuxProductPart2
import Breakdown.Uniqueness.RegEmbedAux

open scoped ContDiff ENNReal FourierTransform
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace ProfileSymbolEquationInternal

theorem aesm_of_continuousOn {E : Type*} [NormedAddCommGroup E] {g : Space → E}
    (hg : ContinuousOn g {ξ : Space | ξ ≠ 0}) : AEStronglyMeasurable g volume := by
  have h1 : AEStronglyMeasurable g (volume.restrict ({0}ᶜ : Set Space)) :=
    hg.aestronglyMeasurable isClosed_singleton.isOpen_compl.measurableSet
  rwa [restrict_compl_singleton] at h1

theorem integrable_of_rpow_bound {E : Type*} [NormedAddCommGroup E] {g : Space → E}
    (hm : AEStronglyMeasurable g volume) {R C β : ℝ} (hβ : -3 < β)
    (hR : ∀ ξ : Space, R < ‖ξ‖ → g ξ = 0) (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) :
    Integrable g := by
  have hae : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hball : IntegrableOn g (Metric.ball 0 (|R| + 1)) volume := by
    refine integrableOn_ball_of_norm_le_rpow (by simp) (α := -β) (C := C) ?_ ?_ hm
    · simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
      linarith
    · exact ae_restrict_of_ae (hae.mono fun ξ hξ => by rw [neg_neg]; exact hC ξ hξ)
  refine hball.integrable_of_forall_notMem_eq_zero fun ξ hξ => ?_
  have : |R| + 1 ≤ ‖ξ‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hξ
  exact hR ξ (by linarith [le_abs_self R])

theorem bound_max {E : Type*} [NormedAddCommGroup E] {g : Space → E} {C β : ℝ}
    (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) :
    ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ max C 0 * ‖ξ‖ ^ β := fun ξ hξ =>
  (hC ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))

theorem comp_bound {E : Type*} [NormedAddCommGroup E] {g : Space → E} {C β : ℝ} (hC0 : 0 ≤ C)
    (hβ : β ≤ 0) (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) {c : ℝ} (hc : 0 < c)
    {ζ η : Space} (hη : η ≠ 0) (h : c * ‖η‖ ≤ ‖ζ‖) : ‖g ζ‖ ≤ (C * c ^ β) * ‖η‖ ^ β := by
  have hpos : 0 < c * ‖η‖ := mul_pos hc (norm_pos_iff.2 hη)
  have hζ : ζ ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hpos h)
  calc ‖g ζ‖ ≤ C * ‖ζ‖ ^ β := hC ζ hζ
    _ ≤ C * (c * ‖η‖) ^ β := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos h hβ) hC0
    _ = (C * c ^ β) * ‖η‖ ^ β := by rw [Real.mul_rpow hc.le (norm_nonneg _)]; ring

theorem char_continuous (y : Space) :
    Continuous (fun ξ : Space => ((𝐞 (inner ℝ ξ y) : Circle) : ℂ)) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))

theorem integrable_char_smul {g : Space → Freq.CSpace} (hg : Integrable g) (y : Space) :
    Integrable (fun ξ : Space => ((𝐞 (inner ℝ ξ y) : Circle) : ℂ) • g ξ) := by
  refine hg.norm.mono' ((char_continuous y).aestronglyMeasurable.smul hg.1)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_smul, Circle.norm_coe, one_mul]

theorem param_hasDerivAt {α : ℝ} (hα : 1 < α) (hα' : α < 5 / 4) {w : Space → Freq.CSpace}
    (hw : IsProfileSymbol α w) (y : Space) (L L' : ℝ → Space →L[ℝ] Space) {t₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ nhds t₀) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hlow : ∀ t ∈ s, ∀ η, c * ‖η‖ ≤ ‖L t η‖) (hup : ∀ t ∈ s, ∀ η, ‖L' t η‖ ≤ K * ‖η‖)
    (hL : ∀ t ∈ s, ∀ η, HasDerivAt (fun t => L t η) (L' t η) t) :
    HasDerivAt (fun t => ∫ η, ((𝐞 (inner ℝ η y) : Circle) : ℂ) • w (L t η))
      (∫ η, ((𝐞 (inner ℝ η y) : Circle) : ℂ) • fderiv ℝ w (L t₀ η) (L' t₀ η)) t₀ := by
  obtain ⟨R, hR⟩ := hw.2.1
  obtain ⟨C0, hC0⟩ := hw.2.2.1 0
  obtain ⟨C1, hC1⟩ := hw.2.2.1 1
  have hb0 : ∀ ξ : Space, ξ ≠ 0 → ‖w ξ‖ ≤ max C0 0 * ‖ξ‖ ^ (2 * α - 4) := bound_max fun ξ hξ => by
    have := hC0 ξ hξ
    rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at this
  have hb1 : ∀ ξ : Space, ξ ≠ 0 → ‖fderiv ℝ w ξ‖ ≤ max C1 0 * ‖ξ‖ ^ (2 * α - 5) := bound_max fun ξ hξ => by
    have := hC1 ξ hξ
    rw [norm_iteratedFDeriv_one, Nat.cast_one] at this
    rwa [show 2 * α - 4 - 1 = 2 * α - 5 by ring] at this
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  have hopen : IsOpen {ξ : Space | ξ ≠ 0} := isOpen_ne
  have hcont : ContinuousOn w {ξ : Space | ξ ≠ 0} := hw.1.continuousOn
  have hdcont : ContinuousOn (fun ξ => fderiv ℝ w ξ) {ξ : Space | ξ ≠ 0} :=
    hw.1.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hne : ∀ t ∈ s, ∀ η : Space, η ≠ 0 → L t η ≠ 0 := by
    intro t ht η hη h
    have h1 := hlow t ht η
    rw [h, norm_zero] at h1
    have : 0 < c * ‖η‖ := mul_pos hc (norm_pos_iff.2 hη)
    linarith
  have hzero : ∀ ξ : Space, R < ‖ξ‖ → fderiv ℝ w ξ = 0 := by
    intro ξ hξ
    have hev : w =ᶠ[nhds ξ] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hξ] with ζ hζ
      exact hR ζ hζ
    rw [hev.fderiv_eq]
    simp
  have hfar : ∀ t ∈ s, ∀ η : Space, R / c < ‖η‖ → R < ‖L t η‖ := by
    intro t ht η hη
    have := (div_lt_iff₀ hc).1 hη
    linarith [hlow t ht η]
  set M : ℝ := (max C1 0 * c ^ (2 * α - 5)) * K with hM
  have hM0 : 0 ≤ M := mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hc.le _)) hK
  set bnd : Space → ℝ := Set.indicator {η : Space | ‖η‖ ≤ R / c} (fun η => M * ‖η‖ ^ (2 * α - 4))
  have hbnd_int : Integrable bnd := by
    refine integrable_of_rpow_bound (R := R / c) (C := M) (β := 2 * α - 4) ?_ (by linarith) ?_ ?_
    · exact ((measurable_const.mul (measurable_norm.pow_const _)).indicator
        (measurableSet_le measurable_norm measurable_const)).aestronglyMeasurable
    · intro ξ hξ
      simp only [bnd, Set.indicator, Set.mem_ofPred_eq]
      rw [if_neg (not_le.2 hξ)]
    · intro ξ _
      simp only [bnd, Set.indicator, Set.mem_ofPred_eq]
      split_ifs
      · rw [Real.norm_of_nonneg (mul_nonneg hM0 (Real.rpow_nonneg (norm_nonneg _) _))]
      · simp only [norm_zero]; exact mul_nonneg hM0 (Real.rpow_nonneg (norm_nonneg _) _)
  have hae : ∀ᵐ η ∂(volume : Measure Space), η ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hmeas : ∀ t ∈ s, AEStronglyMeasurable
      (fun η => ((𝐞 (inner ℝ η y) : Circle) : ℂ) • w (L t η)) volume := by
    intro t ht
    exact aesm_of_continuousOn ((char_continuous y).continuousOn.smul
      (hcont.comp (L t).continuous.continuousOn fun η hη => hne t ht η hη))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.eventually_of_mem hs hmeas) ?_
    (F' := fun t η => ((𝐞 (inner ℝ η y) : Circle) : ℂ) • fderiv ℝ w (L t η) (L' t η)) ?_ ?_ hbnd_int ?_).2
  · refine integrable_char_smul ?_ y
    refine integrable_of_rpow_bound (R := R / c) (C := max C0 0 * c ^ (2 * α - 4)) (β := 2 * α - 4)
      (aesm_of_continuousOn (hcont.comp (L t₀).continuous.continuousOn fun η hη => hne t₀ ht₀ η hη))
      (by linarith) (fun η hη => hR _ (hfar t₀ ht₀ η hη)) ?_
    intro η hη
    exact comp_bound (le_max_right _ _) (by linarith) hb0 hc hη (hlow t₀ ht₀ η)
  · exact aesm_of_continuousOn ((char_continuous y).continuousOn.smul
      ((hdcont.comp (L t₀).continuous.continuousOn fun η hη => hne t₀ ht₀ η hη).clm_apply
        (L' t₀).continuous.continuousOn))
  · filter_upwards [hae] with η hη t ht
    rw [norm_smul, Circle.norm_coe, one_mul]
    by_cases hfarη : R / c < ‖η‖
    · rw [hzero _ (hfar t ht η hfarη)]
      simp only [ContinuousLinearMap.zero_apply, norm_zero, bnd, Set.indicator]
      split_ifs
      · exact mul_nonneg hM0 (Real.rpow_nonneg (norm_nonneg _) _)
      · exact le_rfl
    · have hin : η ∈ {η : Space | ‖η‖ ≤ R / c} := not_lt.1 hfarη
      simp only [bnd, Set.indicator_of_mem hin]
      have hpos : 0 < ‖η‖ := norm_pos_iff.2 hη
      calc ‖fderiv ℝ w (L t η) (L' t η)‖ ≤ ‖fderiv ℝ w (L t η)‖ * ‖L' t η‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ((max C1 0 * c ^ (2 * α - 5)) * ‖η‖ ^ (2 * α - 5)) * (K * ‖η‖) :=
            mul_le_mul (comp_bound (le_max_right _ _) (by linarith) hb1 hc hη (hlow t ht η))
              (hup t ht η) (norm_nonneg _) (by positivity)
        _ = M * ‖η‖ ^ (2 * α - 4) := by
            rw [hM, show 2 * α - 4 = (2 * α - 5) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
            ring
  · filter_upwards [hae] with η hη t ht
    have hζ := hne t ht η hη
    have hd : HasFDerivAt w (fderiv ℝ w (L t η)) (L t η) :=
      ((hw.1.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hζ)).hasFDerivAt
    exact (hd.comp_hasDerivAt t (hL t ht η)).const_smul (((𝐞 (inner ℝ η y) : Circle) : ℂ))


theorem integral_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (g : Space → E) (y : Space) :
    𝓕⁻ g y = ∫ ξ, ((𝐞 (inner ℝ ξ y) : Circle) : ℂ) • g ξ := by
  rw [Real.fourierInv_eq]
  simp only [Circle.smul_def]

theorem scale_identity {α : ℝ} (hα : 1 < α) (hα' : α < 5 / 4) {w : Space → Freq.CSpace}
    (hw : IsProfileSymbol α w) (y : Space) {D : Space →L[ℝ] Freq.CSpace}
    (hD : HasFDerivAt (𝓕⁻ w) D y) :
    D y = (-3 : ℝ) • 𝓕⁻ w y - 𝓕⁻ (fun ξ => fderiv ℝ w ξ ξ) y := by
  have hs : Set.Ioo (1 / 2 : ℝ) 2 ∈ nhds (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hB := param_hasDerivAt hα hα' hw y (fun t => t⁻¹ • ContinuousLinearMap.id ℝ Space)
    (fun t => (-(t ^ 2)⁻¹) • ContinuousLinearMap.id ℝ Space) hs (c := 1 / 2) (K := 4)
    (by norm_num) (by norm_num)
    (fun t ht η => by
      have ht0 : 0 < t := by linarith [ht.1]
      have h2 : (2 : ℝ)⁻¹ ≤ t⁻¹ := inv_anti₀ ht0 ht.2.le
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_right (by simpa using h2) (norm_nonneg _))
    (fun t ht η => by
      have ht0 : 0 < t := by linarith [ht.1]
      have h4 : (t ^ 2)⁻¹ ≤ 4 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]
        nlinarith [ht.1]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        Real.norm_eq_abs, abs_neg, abs_inv, abs_of_pos (pow_pos ht0 2)]
      exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _))
    (fun t ht η => by
      have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith [ht.1]).ne'
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      exact (hasDerivAt_inv ht0).smul_const η)
  have hGB : ∀ t : ℝ, 0 < t → 𝓕⁻ w (t • y) =
      (t ^ 3)⁻¹ • ∫ η, ((𝐞 (inner ℝ η y) : Circle) : ℂ) •
        w ((t⁻¹ • ContinuousLinearMap.id ℝ Space) η) := by
    intro t ht
    have hcv := Measure.integral_comp_smul (μ := (volume : Measure Space))
      (f := fun η : Space => ((𝐞 (inner ℝ η y) : Circle) : ℂ) • w (t⁻¹ • η)) (R := t)
    rw [finrank_euclideanSpace, Fintype.card_fin, abs_of_pos (by positivity)] at hcv
    simp only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, real_inner_smul_left] at hcv
    rw [integral_form]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_right]
    exact hcv
  have hev : (fun t : ℝ => 𝓕⁻ w (t • y)) =ᶠ[nhds 1] fun t => (t ^ 3)⁻¹ • ∫ η,
      ((𝐞 (inner ℝ η y) : Circle) : ℂ) • w ((t⁻¹ • ContinuousLinearMap.id ℝ Space) η) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hGB t ht
  have hpow : HasDerivAt (fun t : ℝ => (t ^ 3)⁻¹) (-3) 1 := by
    exact ((hasDerivAt_pow 3 (1 : ℝ)).inv (by norm_num)).congr_deriv (by norm_num)
  have h1 := (hpow.smul hB).congr_of_eventuallyEq hev
  have h2 : HasDerivAt (fun t : ℝ => 𝓕⁻ w (t • y)) (D y) 1 := by
    have hD' : HasFDerivAt (𝓕⁻ w) D ((1 : ℝ) • y) := by rwa [one_smul]
    have := hD'.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const y)
    rw [one_smul] at this
    exact this
  have e1 : ∀ η : Space, ((1 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ Space) η = η := fun η => by simp
  have e2 : ∀ η : Space, ((-((1 : ℝ) ^ 2)⁻¹) • ContinuousLinearMap.id ℝ Space) η = -η := fun η => by simp
  rw [h2.unique h1]
  simp only [e1, e2]
  simp only [map_neg, smul_neg, integral_neg, one_pow, inv_one, one_smul, integral_form]
  abel

def planeMap : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (EuclideanSpace.single 0 1) +
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (EuclideanSpace.single 1 1)

def axisMap : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (EuclideanSpace.single 2 1)

def turnMap : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (EuclideanSpace.single 1 1) -
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (EuclideanSpace.single 0 1)

def rotMap (t : ℝ) : Space →L[ℝ] Space := Real.cos t • planeMap + Real.sin t • turnMap + axisMap

def rotMapDeriv (t : ℝ) : Space →L[ℝ] Space := (-Real.sin t) • planeMap + Real.cos t • turnMap

theorem space_ext {a b : Space} (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem rot_apply (t : ℝ) (η : Space) :
    rotMap t η 0 = Real.cos t * η 0 - Real.sin t * η 1 ∧
      rotMap t η 1 = Real.sin t * η 0 + Real.cos t * η 1 ∧ rotMap t η 2 = η 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [rotMap, planeMap, turnMap, axisMap, EuclideanSpace.single_apply] <;> ring

theorem rotDeriv_apply (t : ℝ) (η : Space) :
    rotMapDeriv t η 0 = -Real.sin t * η 0 - Real.cos t * η 1 ∧
      rotMapDeriv t η 1 = -Real.sin t * η 1 + Real.cos t * η 0 ∧ rotMapDeriv t η 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [rotMapDeriv, planeMap, turnMap, EuclideanSpace.single_apply] <;> ring

theorem turnMap_eq (η : Space) : turnMap η = axialTurn η := by
  apply space_ext <;> simp [turnMap, axialTurn, EuclideanSpace.single_apply]

theorem rotMap_zero (η : Space) : rotMap 0 η = η := by
  obtain ⟨h0, h1, h2⟩ := rot_apply 0 η
  apply space_ext
  · rw [h0]; simp
  · rw [h1]; simp
  · rw [h2]

theorem rotMapDeriv_zero (η : Space) : rotMapDeriv 0 η = axialTurn η := by
  obtain ⟨h0, h1, h2⟩ := rotDeriv_apply 0 η
  apply space_ext
  · rw [h0]; simp [axialTurn, EuclideanSpace.single_apply]
  · rw [h1]; simp [axialTurn, EuclideanSpace.single_apply]
  · rw [h2]; simp [axialTurn, EuclideanSpace.single_apply]

theorem rotMap_norm (t : ℝ) (η : Space) : ‖rotMap t η‖ = ‖η‖ := by
  obtain ⟨h0, h1, h2⟩ := rot_apply t η
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_three, h0, h1, h2]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  linear_combination (η 0 ^ 2 + η 1 ^ 2) * Real.sin_sq_add_cos_sq t

theorem rotMap_hasDerivAt (t : ℝ) (η : Space) :
    HasDerivAt (fun t => rotMap t η) (rotMapDeriv t η) t := by
  simp only [rotMap, rotMapDeriv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  exact (((hasDerivAt_cos t).smul_const (planeMap η)).add
    ((hasDerivAt_sin t).smul_const (turnMap η))).add_const (axisMap η)

def rotIso (t : ℝ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨(rotMap t).toLinearMap, fun η => rotMap_norm t η⟩ rfl

theorem rot_identity {α : ℝ} (hα : 1 < α) (hα' : α < 5 / 4) {w : Space → Freq.CSpace}
    (hw : IsProfileSymbol α w) (y : Space) {D : Space →L[ℝ] Freq.CSpace}
    (hD : HasFDerivAt (𝓕⁻ w) D y) :
    D (axialTurn y) = 𝓕⁻ (fun ξ => fderiv ℝ w ξ (axialTurn ξ)) y := by
  have hB := param_hasDerivAt hα hα' hw y rotMap rotMapDeriv (t₀ := 0) Filter.univ_mem (c := 1)
    (K := ‖planeMap‖ + ‖turnMap‖) one_pos (by positivity)
    (fun t _ η => by rw [rotMap_norm, one_mul])
    (fun t _ η => by
      have hn : ‖rotMapDeriv t‖ ≤ ‖planeMap‖ + ‖turnMap‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs, abs_neg]
          exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one t)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one t)
      exact ((rotMapDeriv t).le_opNorm η).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _)))
    (fun t _ η => rotMap_hasDerivAt t η)
  have hGB : ∀ t, 𝓕⁻ w (rotMap t y) = ∫ η, ((𝐞 (inner ℝ η y) : Circle) : ℂ) • w (rotMap t η) := by
    intro t
    rw [integral_form, ← MeasureTheory.integral_comp (rotIso t)]
    congr 1
    funext η
    change ((𝐞 (inner ℝ (rotIso t η) (rotIso t y)) : Circle) : ℂ) • w (rotIso t η) = _
    rw [LinearIsometryEquiv.inner_map_map]
    rfl
  have h2 : HasDerivAt (fun t => 𝓕⁻ w (rotMap t y)) (D (rotMapDeriv 0 y)) 0 := by
    have hD' : HasFDerivAt (𝓕⁻ w) D (rotMap 0 y) := by rwa [rotMap_zero]
    exact hD'.comp_hasDerivAt (0 : ℝ) (rotMap_hasDerivAt 0 y)
  have h1 : HasDerivAt (fun t => 𝓕⁻ w (rotMap t y))
      (∫ η, ((𝐞 (inner ℝ η y) : Circle) : ℂ) • fderiv ℝ w (rotMap 0 η) (rotMapDeriv 0 η)) 0 := by
    simp_rw [hGB]
    exact hB
  have := h2.unique h1
  rw [rotMapDeriv_zero] at this
  rw [this, integral_form]
  congr 1
  funext η
  rw [rotMap_zero, rotMapDeriv_zero]


theorem finv_add {f g : Space → Freq.CSpace} (hf : Integrable f) (hg : Integrable g) (y : Space) :
    𝓕⁻ (fun ξ => f ξ + g ξ) y = 𝓕⁻ f y + 𝓕⁻ g y := by
  rw [integral_form, integral_form, integral_form]
  simp only [smul_add]
  exact integral_add (integrable_char_smul hf y) (integrable_char_smul hg y)

theorem finv_sub {f g : Space → Freq.CSpace} (hf : Integrable f) (hg : Integrable g) (y : Space) :
    𝓕⁻ (fun ξ => f ξ - g ξ) y = 𝓕⁻ f y - 𝓕⁻ g y := by
  rw [integral_form, integral_form, integral_form]
  simp only [smul_sub]
  exact integral_sub (integrable_char_smul hf y) (integrable_char_smul hg y)

theorem finv_smul (r : ℝ) (f : Space → Freq.CSpace) (y : Space) :
    𝓕⁻ (fun ξ => r • f ξ) y = r • 𝓕⁻ f y := by
  rw [integral_form, integral_form, ← integral_smul]
  congr 1
  funext ξ
  rw [smul_comm]

def turnCL : Freq.CSpace →L[ℂ] Freq.CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := axialTurnC
      map_add' := fun x z => by
        ext i
        fin_cases i <;> simp [axialTurnC, EuclideanSpace.single_apply] <;> ring
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp [axialTurnC, EuclideanSpace.single_apply] }

theorem turnCL_apply (z : Freq.CSpace) : turnCL z = axialTurnC z := rfl

theorem finv_turn {f : Space → Freq.CSpace} (hf : Integrable f) (y : Space) :
    𝓕⁻ (fun ξ => axialTurnC (f ξ)) y = axialTurnC (𝓕⁻ f y) := by
  rw [integral_form, integral_form, ← turnCL_apply, ← turnCL.integral_comp_comm (integrable_char_smul hf y)]
  congr 1
  funext ξ
  rw [map_smul, turnCL_apply]

theorem turn_real (z : Freq.CSpace) : axialTurn (Freq.realVec z) = Freq.realVec (axialTurnC z) := by
  apply space_ext <;> simp [axialTurn, axialTurnC, Freq.realVec, EuclideanSpace.single_apply]

theorem sq_bound {E : Type*} [NormedAddCommGroup E] {g : Space → E} {C β : ℝ}
    (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) :
    ∀ ξ : Space, ξ ≠ 0 → ‖‖g ξ‖ ^ 2‖ ≤ C ^ 2 * ‖ξ‖ ^ (2 * β) := by
  intro ξ hξ
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [Real.norm_of_nonneg (by positivity), mul_comm 2 β, Real.rpow_mul hpos.le, Real.rpow_two, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC ξ hξ) 2

end ProfileSymbolEquationInternal

open ProfileSymbolEquationInternal in
theorem profileSymbolEquation : ProfileSymbolEquationStatement := by
  intro α hα hα' a s w hs hw heq
  obtain ⟨R, hR⟩ := hw.2.1
  obtain ⟨C0, hC0⟩ := hw.2.2.1 0
  obtain ⟨C1, hC1⟩ := hw.2.2.1 1
  have hb0 : ∀ ξ : Space, ξ ≠ 0 → ‖w ξ‖ ≤ max C0 0 * ‖ξ‖ ^ (2 * α - 4) := bound_max fun ξ hξ => by
    have := hC0 ξ hξ
    rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at this
  have hb1 : ∀ ξ : Space, ξ ≠ 0 → ‖fderiv ℝ w ξ‖ ≤ max C1 0 * ‖ξ‖ ^ (2 * α - 5) := bound_max fun ξ hξ => by
    have := hC1 ξ hξ
    rw [norm_iteratedFDeriv_one, Nat.cast_one] at this
    rwa [show 2 * α - 4 - 1 = 2 * α - 5 by ring] at this
  have hopen : IsOpen {ξ : Space | ξ ≠ 0} := isOpen_ne
  have hcont : ContinuousOn w {ξ : Space | ξ ≠ 0} := hw.1.continuousOn
  have hdcont : ContinuousOn (fun ξ => fderiv ℝ w ξ) {ξ : Space | ξ ≠ 0} :=
    hw.1.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hzero : ∀ ξ : Space, R < ‖ξ‖ → fderiv ℝ w ξ = 0 := by
    intro ξ hξ
    have hev : w =ᶠ[nhds ξ] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hξ] with ζ hζ
      exact hR ζ hζ
    rw [hev.fderiv_eq]
    simp
  have hwm : AEStronglyMeasurable w volume := aesm_of_continuousOn hcont
  have Iw : Integrable w := integrable_of_rpow_bound hwm (by linarith) hR hb0
  have Iw1 : Integrable (fun v : Space => ‖v‖ * ‖w v‖) := by
    refine integrable_of_rpow_bound (R := R) (C := max C0 0) (β := 2 * α - 3)
      (continuous_norm.aestronglyMeasurable.mul hwm.norm) (by linarith)
      (fun ξ hξ => by simp [hR ξ hξ]) (fun ξ hξ => ?_)
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [Real.norm_of_nonneg (by positivity), show 2 * α - 3 = (2 * α - 4) + 1 by ring,
      Real.rpow_add hpos, Real.rpow_one]
    calc ‖ξ‖ * ‖w ξ‖ ≤ ‖ξ‖ * (max C0 0 * ‖ξ‖ ^ (2 * α - 4)) := mul_le_mul_of_nonneg_left (hb0 ξ hξ) hpos.le
      _ = _ := by ring
  have Idw : ∀ M : Space →L[ℝ] Space, Integrable (fun ξ => fderiv ℝ w ξ (M ξ)) := by
    intro M
    refine integrable_of_rpow_bound (R := R) (C := max C1 0 * ‖M‖) (β := 2 * α - 4)
      (aesm_of_continuousOn (hdcont.clm_apply M.continuous.continuousOn)) (by linarith)
      (fun ξ hξ => by simp [hzero ξ hξ]) (fun ξ hξ => ?_)
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    calc ‖fderiv ℝ w ξ (M ξ)‖ ≤ ‖fderiv ℝ w ξ‖ * ‖M ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (max C1 0 * ‖ξ‖ ^ (2 * α - 5)) * (‖M‖ * ‖ξ‖) :=
          mul_le_mul (hb1 ξ hξ) (M.le_opNorm ξ) (norm_nonneg _) (by positivity)
      _ = _ := by
          rw [show 2 * α - 4 = (2 * α - 5) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
          ring
  have I1 : Integrable (fun ξ => fderiv ℝ w ξ ξ) := Idw (ContinuousLinearMap.id ℝ Space)
  have I2 : Integrable (fun ξ => fderiv ℝ w ξ (axialTurn ξ)) := by
    have := Idw turnMap
    simpa only [turnMap_eq] using this
  have IT : Integrable (fun ξ => axialTurnC (w ξ)) := turnCL.integrable_comp Iw
  have hkm : AEStronglyMeasurable (fun ξ => freqPow (2 * α) ξ • w ξ) volume := by
    unfold freqPow
    exact ((measurable_const.mul measurable_norm).pow_const _).aestronglyMeasurable.smul hwm
  have hkb : ∀ ξ : Space, ξ ≠ 0 → ‖freqPow (2 * α) ξ • w ξ‖ ≤
      ((2 * π) ^ (2 * α) * max C0 0) * ‖ξ‖ ^ (4 * α - 4) := by
    intro ξ hξ
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [norm_smul, freqPow, Real.norm_of_nonneg (by positivity),
      Real.mul_rpow (by positivity) (norm_nonneg _)]
    calc (2 * π) ^ (2 * α) * ‖ξ‖ ^ (2 * α) * ‖w ξ‖ ≤
        (2 * π) ^ (2 * α) * ‖ξ‖ ^ (2 * α) * (max C0 0 * ‖ξ‖ ^ (2 * α - 4)) :=
          mul_le_mul_of_nonneg_left (hb0 ξ hξ) (by positivity)
      _ = _ := by
          rw [show 4 * α - 4 = 2 * α + (2 * α - 4) by ring, Real.rpow_add hpos]
          ring
  have hkR : ∀ ξ : Space, R < ‖ξ‖ → freqPow (2 * α) ξ • w ξ = 0 := fun ξ hξ => by simp [hR ξ hξ]
  have Ik : Integrable (fun ξ => freqPow (2 * α) ξ • w ξ) :=
    integrable_of_rpow_bound hkm (by linarith) hkR hkb
  have Lk : MemLp (fun ξ => freqPow (2 * α) ξ • w ξ) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hkm).2
      (integrable_of_rpow_bound (R := R) (hkm.norm.pow 2) (by linarith)
        (fun ξ hξ => by simp [hkR ξ hξ]) (sq_bound hkb))
  have Is : Integrable s := hs.1.continuous.integrable_of_hasCompactSupport hs.2.1
  have Ls : MemLp s 2 volume := hs.1.continuous.memLp_of_hasCompactSupport hs.2.1
  have hae : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have IA : Integrable (fun ξ => (1 - 2 / α) • w ξ) := Iw.smul (1 - 2 / α)
  have IB : Integrable (fun ξ => (1 / (2 * α)) • fderiv ℝ w ξ ξ) := I1.smul (1 / (2 * α))
  have ICT : Integrable (fun ξ => fderiv ℝ w ξ (axialTurn ξ) - axialTurnC (w ξ)) := I2.sub IT
  have IC : Integrable (fun ξ => a • (fderiv ℝ w ξ (axialTurn ξ) - axialTurnC (w ξ))) := ICT.smul a
  have IAB : Integrable (fun ξ => (1 - 2 / α) • w ξ - (1 / (2 * α)) • fderiv ℝ w ξ ξ) := IA.sub IB
  have IABC : Integrable (fun ξ => (1 - 2 / α) • w ξ - (1 / (2 * α)) • fderiv ℝ w ξ ξ
      + a • (fderiv ℝ w ξ (axialTurn ξ) - axialTurnC (w ξ))) := IAB.add IC
  have hpt : ∀ y, driftField α a (Freq.niceField w) (fun y => fderiv ℝ (Freq.niceField w) y) y
      + Freq.niceField (fun ξ => freqPow (2 * α) ξ • w ξ) y = Freq.niceField s y := by
    intro y
    have hD := SmoothFlow.Internal.hasFDerivAt_freqTrInv Iw Iw1 y
    have hv : HasFDerivAt (Freq.niceField w) (Freq.realVec.comp _) y := Freq.realVec.hasFDerivAt.comp y hD
    have hsc := scale_identity hα hα' hw y hD
    have hrt := rot_identity hα hα' hw y hD
    have hsw : 𝓕⁻ s y = 𝓕⁻ (profileSymbolLhs α a w) y := by
      rw [integral_form, integral_form]
      refine integral_congr_ae ?_
      filter_upwards [hae] with ξ hξ
      rw [heq ξ hξ]
    have hs_eq : 𝓕⁻ s y = (1 - 2 / α) • 𝓕⁻ w y - (1 / (2 * α)) • 𝓕⁻ (fun ξ => fderiv ℝ w ξ ξ) y
        + a • (𝓕⁻ (fun ξ => fderiv ℝ w ξ (axialTurn ξ)) y - axialTurnC (𝓕⁻ w y))
        + 𝓕⁻ (fun ξ => freqPow (2 * α) ξ • w ξ) y := by
      rw [hsw, show profileSymbolLhs α a w = fun ξ => (1 - 2 / α) • w ξ - (1 / (2 * α)) • fderiv ℝ w ξ ξ
          + a • (fderiv ℝ w ξ (axialTurn ξ) - axialTurnC (w ξ)) + freqPow (2 * α) ξ • w ξ from rfl,
        finv_add IABC Ik y, finv_add IAB IC y, finv_sub IA IB y, finv_smul, finv_smul, finv_smul,
        finv_sub I2 IT y, finv_turn Iw y]
    simp only [driftField]
    rw [hv.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [hsc, hrt]
    simp only [Freq.niceField]
    rw [hs_eq, turn_real]
    simp only [map_add, map_sub, map_smul]
    module
  refine ⟨?_, Filter.Eventually.of_forall hpt⟩
  have hfun : driftField α a (Freq.niceField w) (fun y => fderiv ℝ (Freq.niceField w) y) =
      fun y => Freq.niceField s y - Freq.niceField (fun ξ => freqPow (2 * α) ξ • w ξ) y :=
    funext fun y => eq_sub_of_add_eq (hpt y)
  rw [hfun]
  exact (SmoothFlow.Internal.RegEmbed.memLp_realVec_freqTrInv Is Ls).sub
    (SmoothFlow.Internal.RegEmbed.memLp_realVec_freqTrInv Ik Lk)

end SteadyCert

end Breakdown
