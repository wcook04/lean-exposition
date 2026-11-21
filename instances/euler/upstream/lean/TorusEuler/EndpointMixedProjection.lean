import TorusEuler.AngularLeraySymbol
import TorusEuler.PeriodicLerayReal
import TorusEuler.EndpointMeanFubini
import TorusEuler.EndpointL2Multiplier
import TorusEuler.EndpointMixedEmbedding

/-! The joint weak projection and its time-valued Fourier symbol in Appendix A. -/

open MeasureTheory Set UnitAddTorus
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "μt" => fun T : ℝ => volume.restrict (Ioc 0 T)
local notation "H(" T ")" => Lp Vec3 2 (μt T)

local instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)))

/-- A real Fourier character, including both the cosine and sine phases. -/
def endpointRealFourierCharacter (k : Fin 3 → ℤ) (c : ℂ) : C(A, ℝ) :=
  ⟨fun a => (c * mFourier k a).re,
    Complex.continuous_re.comp (continuous_const.mul (mFourier k).continuous)⟩

private def endpointModeWeight (χ : C(A, ℝ)) :
    ℝ × A → (Vec3 →L[ℝ] Vec3) :=
  fun q => χ q.2 • ContinuousLinearMap.id ℝ Vec3

private theorem endpointModeWeight_aestronglyMeasurable (T : ℝ) (χ : C(A, ℝ)) :
    AEStronglyMeasurable (endpointModeWeight χ) (endpointTorusMeasure T) :=
  ((χ.continuous.comp continuous_snd).smul continuous_const).aestronglyMeasurable

private theorem norm_endpointModeWeight_le (T : ℝ) (χ : C(A, ℝ)) :
    ∀ᵐ q ∂endpointTorusMeasure T, ‖endpointModeWeight χ q‖ ≤ ‖χ‖ := by
  exact ae_of_all _ fun q => by
    rw [endpointModeWeight, norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (χ.norm_coe_le_norm q.2)

private theorem endpointFst_measurePreserving (T : ℝ) :
    MeasurePreserving (Prod.fst : ℝ × A → ℝ) (endpointTorusMeasure T) (μt T) :=
  measurePreserving_fst

/-- Insert a real spatial character with a vector-valued time path as its amplitude. -/
def endpointJointModeInsert (T : ℝ) (χ : C(A, ℝ)) : H(T) →L[ℝ] EndpointTorusL2 T :=
  (endpointL2Multiplier (endpointModeWeight χ) (endpointModeWeight_aestronglyMeasurable T χ)
    (norm_endpointModeWeight_le T χ)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (endpointFst_measurePreserving T)).toContinuousLinearMap

theorem endpointJointModeInsert_apply_ae (T : ℝ) (χ : C(A, ℝ)) (w : H(T)) :
    endpointJointModeInsert T χ w =ᵐ[endpointTorusMeasure T] fun q => χ q.2 • w q.1 := by
  let w' := Lp.compMeasurePreserving Prod.fst (endpointFst_measurePreserving T) w
  have hinsert := endpointL2Multiplier_apply_ae (endpointModeWeight χ)
    (endpointModeWeight_aestronglyMeasurable T χ) (norm_endpointModeWeight_le T χ) w'
  filter_upwards [hinsert, Lp.coeFn_compMeasurePreserving w (endpointFst_measurePreserving T)]
    with q h₁ h₂
  change endpointJointModeInsert T χ w q = endpointModeWeight χ q (w' q) at h₁
  change w' q = w q.1 at h₂
  rw [h₁, h₂]
  rfl

/-- The time-valued cosine or sine Fourier coefficient is adjoint to insertion
of the corresponding real character. -/
def endpointJointRealFourierCoefficient (T : ℝ) (k : Fin 3 → ℤ) (c : ℂ) :
    EndpointTorusL2 T →L[ℝ] H(T) :=
  (endpointJointModeInsert T (endpointRealFourierCharacter k c)).adjoint

private theorem endpointRealFourierCharacter_gradient (k : Fin 3 → ℤ) (c : ℂ) :
    ∃ p : EndpointSmoothPotential, ∀ a : A,
      endpointPotentialGradient p a =
        endpointRealFourierCharacter k c a • realFourierFrequency k := by
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hC : C ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (c / C))
  refine ⟨endpointFourierPotential L k, fun a => ?_⟩
  rw [endpointPotentialGradient_fourierPotential]
  change (c / C * (C * mFourier k a)).re • realFourierFrequency k =
    (c * mFourier k a).re • realFourierFrequency k
  rw [← mul_assoc, div_mul_cancel₀ c hC]

private theorem realFourierMode_gradientPair_eq_zero (k : Fin 3 → ℤ) (c : ℂ) (z : Vec3)
    (hz : ⟪realFourierFrequency k, z⟫_ℝ = 0) (p : EndpointSmoothPotential) :
    (∫ a, ⟪endpointPotentialGradient p a, endpointRealFourierCharacter k c a • z⟫_ℝ
      ∂unitTorusMeasure) = 0 := by
  have hcontraction : frequencyContraction k (periodicComplexifyVector z).ofLp = 0 := by
    rw [PiLp.inner_apply] at hz
    have hc : frequencyContraction k (periodicComplexifyVector z).ofLp =
        ((∑ i : Fin 3, ⟪(realFourierFrequency k) i, z i⟫_ℝ) : ℝ) := by
      simp [frequencyContraction, complexFrequency, realFourierFrequency, RCLike.inner_apply, mul_comm]
    rw [hc, hz, Complex.ofReal_zero]
  let b := c • periodicComplexifyVector z
  have hb : b ∈ transverseModeSpace k :=
    (transverseModeSpace k).smul_mem c
      ((mem_transverseModeSpace_iff k (periodicComplexifyVector z).ofLp).mpr hcontraction)
  have hfix : lerayModeProjection k b = b := Submodule.starProjection_eq_self_iff.mpr hb
  let v := periodicL2Mode k b
  have hv : periodicComplexLeray v = v := by
    change periodicComplexLeray (periodicL2Mode k b) = periodicL2Mode k b
    rw [periodicComplexLeray_mode, hfix]
  have hsol := periodicRealPartL2_leray_mem_endpointSpatialSolenoidal v
  rw [hv] at hsol
  have hp := (mem_endpointSpatialSolenoidal _).mp hsol p
  have hrep : periodicRealPartL2 v =ᵐ[unitTorusMeasure]
      fun a => endpointRealFourierCharacter k c a • z := by
    filter_upwards [periodicRealPartL2_apply_ae v, periodicL2Mode_apply_ae k b] with a h₁ h₂
    change v a = _ at h₂
    rw [h₁, h₂]
    apply PiLp.ext
    intro i
    change ((mFourier k a) * (c * (z i : ℂ))).re = (c * mFourier k a).re * z i
    rw [← mul_assoc, mul_comm (mFourier k a), Complex.mul_re]
    simp
  have hpair := hrep.mono fun a ha =>
    congrArg (fun y : Vec3 => ⟪endpointPotentialGradient p a, y⟫_ℝ) ha
  exact (integral_congr_ae hpair).symm.trans hp

private theorem endpointJointModeInsert_mem {T : ℝ} (k : Fin 3 → ℤ) (c : ℂ)
    (w : H(T)) (hm : endpointIntegral T w = 0)
    (ht : ∀ᵐ t ∂μt T, ⟪realFourierFrequency k, w t⟫_ℝ = 0) :
    endpointJointModeInsert T (endpointRealFourierCharacter k c) w ∈ endpointTorusSpace T := by
  let χ := endpointRealFourierCharacter k c
  have hmode := endpointJointModeInsert_apply_ae T χ w
  rw [mem_endpointTorusSpace_iff_slices]
  constructor
  · filter_upwards [ae_endpointTimeSlice_congr hmode] with a ha
    change (∫ t in Ioc 0 T, endpointJointModeInsert T χ w (t, a)) = 0
    rw [integral_congr_ae ha, integral_smul, ← endpointIntegral_apply, hm, smul_zero]
  · intro p
    have hspace := Measure.ae_ae_of_ae_prod hmode
    filter_upwards [hspace, ht] with t hrep htrans
    change (∫ a, ⟪endpointPotentialGradient p a, endpointJointModeInsert T χ w (t, a)⟫_ℝ
      ∂unitTorusMeasure) = 0
    rw [integral_congr_ae (hrep.mono fun a ha =>
      congrArg (fun v : Vec3 => ⟪endpointPotentialGradient p a, v⟫_ℝ) ha)]
    exact realFourierMode_gradientPair_eq_zero k c (w t) htrans p

private theorem endpointJointModeInsert_inner {T : ℝ} (χ : C(A, ℝ)) (w : H(T))
    (v : EndpointTorusL2 T) :
    ⟪endpointJointModeInsert T χ w, v⟫_ℝ =
      ∫ q, ⟪χ q.2 • w q.1, v q⟫_ℝ ∂endpointTorusMeasure T := by
  rw [L2.inner_def]
  exact integral_congr_ae ((endpointJointModeInsert_apply_ae T χ w).mono fun q hq =>
    congrArg (fun x : Vec3 => ⟪x, v q⟫_ℝ) hq)

private theorem integrable_endpointJointModeInsert_inner {T : ℝ} (χ : C(A, ℝ)) (w : H(T))
    (v : EndpointTorusL2 T) :
    Integrable (fun q => ⟪χ q.2 • w q.1, v q⟫_ℝ) (endpointTorusMeasure T) :=
  (L2.integrable_inner (𝕜 := ℝ) (endpointJointModeInsert T χ w) v).congr
    ((endpointJointModeInsert_apply_ae T χ w).mono fun q hq =>
    congrArg (fun x : Vec3 => ⟪x, v q⟫_ℝ) hq)

private theorem endpointJointModeInsert_const_inner_eq_zero {T : ℝ} (χ : C(A, ℝ)) (z : Vec3)
    (v : EndpointTorusL2 T) (hv : v ∈ endpointTorusSpace T) :
    ⟪endpointJointModeInsert T χ (Lp.const 2 (μt T) z), v⟫_ℝ = 0 := by
  let w : H(T) := Lp.const 2 (μt T) z
  have hw := Lp.coeFn_const 2 (μt T) z
  have hwjoint := (endpointFst_measurePreserving T).quasiMeasurePreserving.ae_eq_comp hw
  have heq : (fun q : ℝ × A => ⟪χ q.2 • w q.1, v q⟫_ℝ) =ᵐ[endpointTorusMeasure T]
      fun q => ⟪χ q.2 • z, v q⟫_ℝ := by
    filter_upwards [hwjoint] with q hq
    change w q.1 = z at hq
    rw [hq]
  have hI := (integrable_endpointJointModeInsert_inner χ w v).congr heq
  change ⟪endpointJointModeInsert T χ w, v⟫_ℝ = 0
  rw [endpointJointModeInsert_inner, integral_congr_ae heq]
  change (∫ q, ⟪χ q.2 • z, v q⟫_ℝ ∂(μt T).prod unitTorusMeasure) = 0
  rw [integral_prod_symm _ hI]
  have hmean := ((mem_endpointTorusSpace_iff_slices T v).mp hv).1
  have htime : (fun a : A => ∫ t, ⟪χ a • z, v (t, a)⟫_ℝ ∂μt T) =ᵐ[unitTorusMeasure] 0 := by
    filter_upwards [hmean, ae_memLp_endpointTimeSlice (Lp.memLp v)] with a ha hi
    change (∫ t, innerSL ℝ (χ a • z) (v (t, a)) ∂μt T) = 0
    rw [(innerSL ℝ (χ a • z)).integral_comp_comm (hi.integrable (by norm_num))]
    change (∫ t, v (t, a) ∂μt T) = 0 at ha
    rw [ha, map_zero]
  rw [integral_congr_ae htime]
  exact integral_zero _ _

private theorem endpointJointModeInsert_longitudinal_inner_eq_zero {T : ℝ}
    (k : Fin 3 → ℤ) (c : ℂ) (w : H(T)) {η : ℝ → ℝ}
    (hw : ∀ᵐ t ∂μt T, w t = η t • realFourierFrequency k)
    (v : EndpointTorusL2 T) (hv : v ∈ endpointTorusSpace T) :
    ⟪endpointJointModeInsert T (endpointRealFourierCharacter k c) w, v⟫_ℝ = 0 := by
  let χ := endpointRealFourierCharacter k c
  obtain ⟨p, hp⟩ := endpointRealFourierCharacter_gradient k c
  have hI := integrable_endpointJointModeInsert_inner χ w v
  rw [endpointJointModeInsert_inner]
  change (∫ q, ⟪χ q.2 • w q.1, v q⟫_ℝ ∂(μt T).prod unitTorusMeasure) = 0
  rw [integral_prod _ hI]
  have hdiv := ((mem_endpointTorusSpace_iff_slices T v).mp hv).2 p
  have htime : (fun t => ∫ a, ⟪χ a • w t, v (t, a)⟫_ℝ ∂unitTorusMeasure) =ᵐ[μt T] 0 := by
    filter_upwards [hdiv, hw] with t ht hη
    change (∫ a, ⟪endpointPotentialGradient p a, v (t, a)⟫_ℝ ∂unitTorusMeasure) = 0 at ht
    change (∫ a, ⟪χ a • w t, v (t, a)⟫_ℝ ∂unitTorusMeasure) = 0
    have heq (a : A) : ⟪χ a • w t, v (t, a)⟫_ℝ =
        η t * ⟪endpointPotentialGradient p a, v (t, a)⟫_ℝ := by
      have hgrad : endpointPotentialGradient p a = χ a • realFourierFrequency k := hp a
      rw [hη, hgrad, smul_comm (χ a) (η t), real_inner_smul_left]
    simp_rw [heq]
    rw [integral_const_mul, ht, mul_zero]
  rw [integral_congr_ae htime]
  exact integral_zero _ _

private instance (T : ℝ) : (endpointTorusSpace T).HasOrthogonalProjection :=
  let : CompleteSpace (endpointTorusSpace T) :=
    (isClosed_endpointTorusSpace T).completeSpace_coe
  inferInstance

/-- The joint orthogonal projection imposing both endpoint constraints. -/
def endpointJointConstraintProjection (T : ℝ) :
    EndpointTorusL2 T →L[ℝ] EndpointTorusL2 T :=
  (endpointTorusSpace T).starProjection

theorem range_endpointJointConstraintProjection (T : ℝ) :
    (endpointJointConstraintProjection T).range = endpointTorusSpace T :=
  (endpointTorusSpace T).range_starProjection

theorem real_inner_angularLeray_eq_zero (ξ z : Vec3) :
    ⟪ξ, angularLeray ξ z⟫_ℝ = 0 := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hξ)
    rw [angularLeray_apply, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, div_mul_cancel₀ _ hn, sub_self]

theorem ae_real_inner_angularTimeLeray_eq_zero (T : ℝ) (ξ : Vec3) (w : H(T)) :
    ∀ᵐ t ∂μt T, ⟪ξ, angularTimeLeray T ξ w t⟫_ℝ = 0 := by
  filter_upwards [angularTimeLeray_apply_ae T ξ w] with t ht
  exact (congrArg (fun z : Vec3 => ⟪ξ, z⟫_ℝ) ht).trans
    (real_inner_angularLeray_eq_zero ξ (endpointSubtractMean T w t))

/-- A path is fixed by the combined symbol exactly when its time mean
and its longitudinal component vanish. -/
theorem angularTimeLeray_eq_self_iff {T : ℝ} (hT : 0 < T) (ξ : Vec3) (w : H(T)) :
    angularTimeLeray T ξ w = w ↔
      endpointIntegral T w = 0 ∧ ∀ᵐ t ∂μt T, ⟪ξ, w t⟫_ℝ = 0 := by
  constructor
  · intro hw
    exact ⟨hw ▸ endpointIntegral_angularTimeLeray hT ξ w,
      hw ▸ ae_real_inner_angularTimeLeray_eq_zero T ξ w⟩
  · rintro ⟨hm, hξ⟩
    have hQ : endpointSubtractMean T w = w := by
      rw [endpointSubtractMean_apply, hm, smul_zero]
      have hconst : Lp.const 2 (μt T) (0 : Vec3) = 0 := by
        apply Lp.ext
        exact (Lp.coeFn_const 2 (μt T) (0 : Vec3)).trans
          (Lp.coeFn_zero (E := Vec3) (p := 2) (μ := μt T)).symm
      rw [hconst, sub_zero]
    apply Lp.ext
    filter_upwards [angularTimeLeray_apply_ae T ξ w, hξ] with t hp ht
    exact hp.trans (by rw [hQ, angularLeray_apply, ht, zero_div, zero_smul, sub_zero])

theorem endpointSubtractMean_apply_ae (T : ℝ) (w : H(T)) :
    ⇑(endpointSubtractMean T w) =ᵐ[μt T]
      fun t => w t - T⁻¹ • endpointIntegral T w := by
  let c := T⁻¹ • endpointIntegral T w
  rw [endpointSubtractMean_apply]
  filter_upwards [Lp.coeFn_sub w (Lp.const 2 (μt T) c),
    Lp.coeFn_const 2 (μt T) c] with t hsub hc
  simp only [hsub, Pi.sub_apply, hc, Function.const_apply, c]

/-- The complementary symbol discards a constant time mean and a path
parallel to the spatial wave vector. -/
theorem ae_sub_angularTimeLeray_eq (T : ℝ) (ξ : Vec3) (w : H(T)) :
    ⇑(w - angularTimeLeray T ξ w) =ᵐ[μt T]
      fun t => T⁻¹ • endpointIntegral T w +
        (⟪ξ, endpointSubtractMean T w t⟫_ℝ / ‖ξ‖ ^ 2) • ξ := by
  filter_upwards [Lp.coeFn_sub w (angularTimeLeray T ξ w),
    angularTimeLeray_apply_ae T ξ w, endpointSubtractMean_apply_ae T w]
    with t hsub hp hQ
  rw [hsub, Pi.sub_apply, hp, angularLeray_apply]
  nth_rewrite 1 [hQ]
  abel


/-- On a spatial Fourier mode the joint weak projection acts on the amplitude
by the combined time-mean and angular Leray symbol. -/
theorem endpointJointConstraintProjection_mode {T : ℝ} (hT : 0 < T)
    (k : Fin 3 → ℤ) (c : ℂ) (w : H(T)) :
    endpointJointConstraintProjection T (endpointJointModeInsert T (endpointRealFourierCharacter k c) w) =
      endpointJointModeInsert T (endpointRealFourierCharacter k c) (angularTimeLeray T (realFourierFrequency k) w) := by
  let ξ := realFourierFrequency k
  let χ := endpointRealFourierCharacter k c
  change (endpointTorusSpace T).starProjection _ = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact endpointJointModeInsert_mem k c _ (endpointIntegral_angularTimeLeray hT ξ w)
      (ae_real_inner_angularTimeLeray_eq_zero T ξ w)
  · intro v hv
    rw [← map_sub]
    let m : Vec3 := T⁻¹ • endpointIntegral T w
    let wconst : H(T) := Lp.const 2 (μt T) m
    let wpar : H(T) := w - angularTimeLeray T ξ w - wconst
    have hpar : ∀ᵐ t ∂μt T, wpar t =
        (⟪ξ, endpointSubtractMean T w t⟫_ℝ / ‖ξ‖ ^ 2) • ξ := by
      filter_upwards [Lp.coeFn_sub (w - angularTimeLeray T ξ w) wconst,
        ae_sub_angularTimeLeray_eq T ξ w, Lp.coeFn_const 2 (μt T) m] with t h₁ h₂ h₃
      change wpar t = _
      rw [h₁, Pi.sub_apply, h₂]
      change wconst t = m at h₃
      rw [h₃]
      dsimp only [m]
      abel
    have hsplit : w - angularTimeLeray T ξ w = wpar + wconst := (sub_add_cancel _ _).symm
    change ⟪endpointJointModeInsert T χ (w - angularTimeLeray T ξ w), v⟫_ℝ = 0
    rw [hsplit, map_add, inner_add_left, endpointJointModeInsert_const_inner_eq_zero χ m v hv]
    exact (add_zero _).trans (endpointJointModeInsert_longitudinal_inner_eq_zero k c wpar hpar v hv)

/-- Every real time-valued Fourier coefficient of the joint weak projection is
given by applying the corresponding combined symbol to the incoming coefficient. -/
theorem endpointJointRealFourierCoefficient_projection {T : ℝ} (hT : 0 < T)
    (k : Fin 3 → ℤ) (c : ℂ) (v : EndpointTorusL2 T) :
    endpointJointRealFourierCoefficient T k c (endpointJointConstraintProjection T v) =
      angularTimeLeray T (realFourierFrequency k) (endpointJointRealFourierCoefficient T k c v) := by
  apply ext_inner_left ℝ
  intro w
  have hsym := (angularTimeLeray_isSymmetricProjection hT (realFourierFrequency k)).2
  have hsymm : ⟪w, angularTimeLeray T (realFourierFrequency k)
      (endpointJointRealFourierCoefficient T k c v)⟫_ℝ =
      ⟪angularTimeLeray T (realFourierFrequency k) w,
        endpointJointRealFourierCoefficient T k c v⟫_ℝ := (hsym _ _).symm
  rw [hsymm, endpointJointRealFourierCoefficient,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  change ⟪endpointJointModeInsert T (endpointRealFourierCharacter k c) w,
      (endpointTorusSpace T).starProjection v⟫_ℝ = _
  rw [← Submodule.inner_starProjection_left_eq_right]
  change ⟪endpointJointConstraintProjection T (endpointJointModeInsert T
    (endpointRealFourierCharacter k c) w), v⟫_ℝ = _
  rw [endpointJointConstraintProjection_mode hT]

/-- The time mean and longitudinal components of each joint Fourier coefficient
vanish for a field satisfying the weak endpoint constraints. -/
theorem endpointJointRealFourierCoefficient_constraints {T : ℝ} (hT : 0 < T)
    {v : EndpointTorusL2 T} (hv : v ∈ endpointTorusSpace T) (k : Fin 3 → ℤ) (c : ℂ) :
    let w := endpointJointRealFourierCoefficient T k c v
    endpointIntegral T w = 0 ∧
      ∀ᵐ t ∂μt T, ⟪realFourierFrequency k, w t⟫_ℝ = 0 := by
  have hp : endpointJointConstraintProjection T v = v :=
    Submodule.starProjection_eq_self_iff.mpr hv
  have hcoeff := endpointJointRealFourierCoefficient_projection hT k c v
  rw [hp] at hcoeff
  exact (angularTimeLeray_eq_self_iff hT _ _).mp hcoeff.symm


/-- The real Fourier coefficient of a spatial half-Hölder field of time
paths agrees with the joint L² coefficient under the mixed embedding. -/
theorem endpointJointRealFourierCoefficient_mixed {T : ℝ}
    (k : Fin 3 → ℤ) (c : ℂ) (w : HalfHolder A H(T)) :
    endpointJointRealFourierCoefficient T k c (endpointMixedToJoint T w) =
      ∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a w ∂unitTorusMeasure := by
  let χ := endpointRealFourierCharacter k c
  let v := endpointMixedToJoint T w
  have hcont : Continuous (fun a => HalfHolder.eval a w) := w.val.1.continuous
  have hI : Integrable (fun a => χ a • HalfHolder.eval a w) unitTorusMeasure :=
    (χ.continuous.smul hcont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply ext_inner_left ℝ
  intro z
  rw [endpointJointRealFourierCoefficient, ContinuousLinearMap.adjoint_inner_right,
    endpointJointModeInsert_inner]
  change (∫ q, ⟪χ q.2 • z q.1, v q⟫_ℝ ∂(μt T).prod unitTorusMeasure) =
    innerSL ℝ z (∫ a, χ a • HalfHolder.eval a w ∂unitTorusMeasure)
  rw [integral_prod_symm _ (integrable_endpointJointModeInsert_inner χ z v),
    ← (innerSL ℝ z).integral_comp_comm hI]
  apply integral_congr_ae
  filter_upwards [endpointMixedToJoint_apply_ae w] with a ha
  change (∫ t, ⟪χ a • z t, v (t, a)⟫_ℝ ∂μt T) =
    innerSL ℝ z (χ a • HalfHolder.eval a w)
  rw [innerSL_apply_apply, real_inner_smul_right, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ha] with t ht
  change (HalfHolder.eval a w) t = v (t, a) at ht
  change ⟪χ a • z t, v (t, a)⟫_ℝ = χ a * ⟪z t, (HalfHolder.eval a w) t⟫_ℝ
  rw [ht, real_inner_smul_left]

/-- The joint orthogonal projection of an embedded half-Hölder field acts by
the combined symbol on its spatial Bochner Fourier moments. -/
theorem endpointJointRealFourierCoefficient_projection_mixed {T : ℝ} (hT : 0 < T)
    (k : Fin 3 → ℤ) (c : ℂ) (w : HalfHolder A H(T)) :
    endpointJointRealFourierCoefficient T k c
      (endpointJointConstraintProjection T (endpointMixedToJoint T w)) =
        angularTimeLeray T (realFourierFrequency k)
          (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a w ∂unitTorusMeasure) := by
  rw [endpointJointRealFourierCoefficient_projection hT,
    endpointJointRealFourierCoefficient_mixed]

/-- The time-valued joint Fourier coefficient is almost everywhere the spatial
Bochner integral of the corresponding real character against each slice. -/
theorem endpointJointRealFourierCoefficient_apply_ae {T : ℝ}
    (k : Fin 3 → ℤ) (c : ℂ) (v : EndpointTorusL2 T) :
    endpointJointRealFourierCoefficient T k c v =ᵐ[μt T]
      fun t => ∫ a, endpointRealFourierCharacter k c a • v (t, a) ∂unitTorusMeasure := by
  let χ := endpointRealFourierCharacter k c
  let u := endpointJointRealFourierCoefficient T k c v
  let f (t : ℝ) : Vec3 := ∫ a, χ a • v (t, a) ∂unitTorusMeasure
  have hu : Integrable u (μt T) := (Lp.memLp u).integrable (by norm_num)
  have hprod : Integrable (fun q : ℝ × A => χ q.2 • v q) ((μt T).prod unitTorusMeasure) :=
    (memLp_endpointL2Mul (endpointModeWeight χ) (endpointModeWeight_aestronglyMeasurable T χ)
      (norm_endpointModeWeight_le T χ) (Lp.memLp v)).integrable (by norm_num)
  have hf : Integrable f (μt T) := hprod.integral_prod_left
  refine Integrable.ae_eq_of_forall_setIntegral_eq u f hu hf fun s hs hm => ?_
  apply ext_inner_left ℝ
  intro z
  let w : H(T) := indicatorConstLp 2 hs hm.ne z
  have hw : w =ᵐ[μt T] s.indicator (fun _ => z) := indicatorConstLp_coeFn
  calc
    ⟪z, ∫ t in s, u t ∂μt T⟫_ℝ = ⟪w, u⟫_ℝ := by
      change innerSL ℝ z (∫ t in s, u t ∂μt T) = _
      rw [← (innerSL ℝ z).integral_comp_comm hu.integrableOn, ← integral_indicator hs, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hw] with t ht
      change s.indicator (fun t => innerSL ℝ z (u t)) t = ⟪w t, u t⟫_ℝ
      rw [ht]
      by_cases h : t ∈ s <;> simp [h, innerSL_apply_apply]
    _ = ⟪endpointJointModeInsert T χ w, v⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ∫ q, ⟪χ q.2 • w q.1, v q⟫_ℝ ∂(μt T).prod unitTorusMeasure :=
      endpointJointModeInsert_inner χ w v
    _ = ⟪z, ∫ t in s, f t ∂μt T⟫_ℝ := by
      rw [integral_prod _ (integrable_endpointJointModeInsert_inner χ w v)]
      change _ = innerSL ℝ z (∫ t in s, f t ∂μt T)
      rw [← (innerSL ℝ z).integral_comp_comm hf.integrableOn, ← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [hw, hprod.prod_right_ae] with t ht hi
      change (∫ a, ⟪χ a • w t, v (t, a)⟫_ℝ ∂unitTorusMeasure) =
        s.indicator (fun t => innerSL ℝ z (f t)) t
      rw [ht]
      by_cases h : t ∈ s
      · simp only [Set.indicator_of_mem h]
        change (∫ a, ⟪χ a • z, v (t, a)⟫_ℝ ∂unitTorusMeasure) =
          innerSL ℝ z (∫ a, χ a • v (t, a) ∂unitTorusMeasure)
        rw [← (innerSL ℝ z).integral_comp_comm hi]
        simp only [innerSL_apply_apply, real_inner_smul_left, real_inner_smul_right]
      · simp [h]

local notation "ν" => unitTorusMeasure

/-- Cosine and sine Fourier moments determine a real spatial L² field. -/
private theorem spatialLp_eq_zero_of_realModes (u : Lp Vec3 2 ν)
    (hre : ∀ k : Fin 3 → ℤ, (∫ a, (mFourier k a).re • u a ∂ν) = 0)
    (him : ∀ k : Fin 3 → ℤ, (∫ a, (mFourier k a).im • u a ∂ν) = 0) :
    u = 0 := by
  have hχ (k : Fin 3 → ℤ) (a : A) : ‖mFourier k a‖ = 1 := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact norm_fourierMode k x
  have hu : Integrable (fun a => u a) ν := (Lp.memLp u).integrable (by norm_num)
  have hcoord (i : Fin 3) : ∀ᵐ a ∂ν, u a i = 0 := by
    let P : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj i
    let L : Vec3 →L[ℝ] ℂ := Complex.ofRealCLM.comp P
    let f : Lp ℂ 2 ν := L.compLpL 2 ν u
    have hrep : f =ᵐ[ν] fun a => (u a i : ℂ) := L.coeFn_compLpL u
    have huf : Integrable (fun a => (u a i : ℂ)) ν := L.integrable_comp hu
    have hpoint_re (k : Fin 3 → ℤ) : (∫ a, (mFourier k a).re * u a i ∂ν) = 0 := by
      have hI : Integrable (fun a => (mFourier k a).re • u a) ν :=
        hu.bdd_smul 1 (Complex.continuous_re.comp (mFourier k).continuous).aestronglyMeasurable
          (ae_of_all ν fun a => by
            rw [Real.norm_eq_abs]
            exact (Complex.abs_re_le_norm (mFourier k a)).trans (hχ k a).le)
      change (∫ a, P ((mFourier k a).re • u a) ∂ν) = 0
      rw [P.integral_comp_comm hI, hre k, map_zero]
    have hpoint_im (k : Fin 3 → ℤ) : (∫ a, (mFourier k a).im * u a i ∂ν) = 0 := by
      have hI : Integrable (fun a => (mFourier k a).im • u a) ν :=
        hu.bdd_smul 1 (Complex.continuous_im.comp (mFourier k).continuous).aestronglyMeasurable
          (ae_of_all ν fun a => by
            rw [Real.norm_eq_abs]
            exact (Complex.abs_im_le_norm (mFourier k a)).trans (hχ k a).le)
      change (∫ a, P ((mFourier k a).im • u a) ∂ν) = 0
      rw [P.integral_comp_comm hI, him k, map_zero]
    have hcoeff (k : Fin 3 → ℤ) : mFourierCoeff f k = 0 := by
      change (∫ a, mFourier (-k) a * f a ∂ν) = 0
      rw [integral_congr_ae (hrep.mono fun a ha =>
        congrArg (fun z : ℂ => mFourier (-k) a * z) ha)]
      have hI : Integrable (fun a => mFourier (-k) a * (u a i : ℂ)) ν :=
        huf.bdd_mul (mFourier (-k)).continuous.aestronglyMeasurable
          (ae_of_all ν fun a => (hχ (-k) a).le)
      apply Complex.ext
      · change Complex.reCLM (∫ a, mFourier (-k) a * (u a i : ℂ) ∂ν) = 0
        rw [← Complex.reCLM.integral_comp_comm hI]
        simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero] using hpoint_re (-k)
      · change Complex.imCLM (∫ a, mFourier (-k) a * (u a i : ℂ) ∂ν) = 0
        rw [← Complex.imCLM.integral_comp_comm hI]
        simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, zero_add] using hpoint_im (-k)
    have hf : f = 0 := by
      have hs : HasSum (fun k : Fin 3 → ℤ =>
          mFourierCoeff f k • (mFourierLp 2 k : Lp ℂ 2 ν)) f :=
        hasSum_mFourier_series_L2 f
      simp_rw [hcoeff, zero_smul] at hs
      exact hs.unique hasSum_zero
    filter_upwards [hrep, (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := ν))] with a ha hzero
    change f a = (u a i : ℂ) at ha
    rw [hf, hzero] at ha
    exact Complex.ofReal_eq_zero.mp ha.symm
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord, (Lp.coeFn_zero (E := Vec3) (p := 2) (μ := ν))] with a ha hzero
  rw [hzero]
  exact PiLp.ext ha


/-- The time-valued real Fourier coefficients separate joint L² fields. -/
theorem endpointJoint_eq_zero_of_fourierCoeff_eq_zero {T : ℝ} {v : EndpointTorusL2 T}
    (h : ∀ (k : Fin 3 → ℤ) (c : ℂ), endpointJointRealFourierCoefficient T k c v = 0) : v = 0 := by
  have hz (k : Fin 3 → ℤ) (c : ℂ) :
      (fun t => ∫ a, endpointRealFourierCharacter k c a • v (t, a) ∂ν) =ᵐ[μt T] 0 := by
    have hk := endpointJointRealFourierCoefficient_apply_ae k c v
    rw [h k c] at hk
    exact hk.symm.trans (Lp.coeFn_zero Vec3 2 (μt T))
  rw [Lp.eq_zero_iff_ae_eq_zero]
  change ∀ᵐ q ∂(μt T).prod ν, v q = 0
  have hmeas : MeasurableSet {q : ℝ × A | v q = 0} :=
    (Lp.stronglyMeasurable v).measurableSet_eq_fun stronglyMeasurable_const
  apply (Measure.ae_prod_iff_ae_ae hmeas).2
  filter_upwards [endpointSpatialSlice_apply_ae v,
    ae_all_iff.mpr (fun k => hz k 1), ae_all_iff.mpr (fun k => hz k (-Complex.I))]
    with t ht hre him
  let u := endpointSpatialSlice v t
  have hrep : u =ᵐ[ν] fun a => v (t, a) := ht
  have hre' (k : Fin 3 → ℤ) : (∫ a, (mFourier k a).re • u a ∂ν) = 0 := by
    rw [integral_congr_ae (hrep.mono fun a ha => congrArg (fun x : Vec3 => (mFourier k a).re • x) ha)]
    simpa [endpointRealFourierCharacter] using hre k
  have him' (k : Fin 3 → ℤ) : (∫ a, (mFourier k a).im • u a ∂ν) = 0 := by
    rw [integral_congr_ae (hrep.mono fun a ha => congrArg (fun x : Vec3 => (mFourier k a).im • x) ha)]
    simpa [endpointRealFourierCharacter, Complex.mul_re] using him k
  have hu : u = 0 := spatialLp_eq_zero_of_realModes u hre' him'
  rw [hu] at hrep
  exact hrep.symm.trans (Lp.coeFn_zero Vec3 2 ν)

/-- The joint endpoint constraints are equivalent to zero time mean and zero
longitudinal components at each real Fourier coefficient. -/
theorem mem_endpointTorusSpace_iff_fourierCoeff {T : ℝ} (hT : 0 < T) (v : EndpointTorusL2 T) :
    v ∈ endpointTorusSpace T ↔
      ∀ (k : Fin 3 → ℤ) (c : ℂ),
        let w := endpointJointRealFourierCoefficient T k c v
        endpointIntegral T w = 0 ∧
          ∀ᵐ t ∂μt T, ⟪realFourierFrequency k, w t⟫_ℝ = 0 := by
  constructor
  · intro hv k c
    exact endpointJointRealFourierCoefficient_constraints hT hv k c
  · intro h
    let p := endpointJointConstraintProjection T v
    have hdiff : v - p = 0 := by
      apply endpointJoint_eq_zero_of_fourierCoeff_eq_zero
      intro k c
      rw [map_sub]
      change endpointJointRealFourierCoefficient T k c v -
        endpointJointRealFourierCoefficient T k c (endpointJointConstraintProjection T v) = 0
      rw [endpointJointRealFourierCoefficient_projection hT]
      rw [(angularTimeLeray_eq_self_iff hT _ _).mpr (h k c), sub_self]
    have hvp : v = p := sub_eq_zero.mp hdiff
    rw [hvp]
    exact (endpointTorusSpace T).starProjection_apply_mem v

/-- Any half-Hölder projection satisfying the real Fourier multiplier formula
agrees with the joint weak orthogonal projection under the mixed embedding. -/
theorem endpointMixedToJoint_eq_projection_of_fourierCoeff {T : ℝ} (hT : 0 < T)
    (w u : HalfHolder A H(T))
    (h : ∀ (k : Fin 3 → ℤ) (c : ℂ),
      (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a u ∂ν) =
        angularTimeLeray T (realFourierFrequency k)
          (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a w ∂ν)) :
    endpointMixedToJoint T u = endpointJointConstraintProjection T (endpointMixedToJoint T w) := by
  apply sub_eq_zero.mp
  apply endpointJoint_eq_zero_of_fourierCoeff_eq_zero
  intro k c
  rw [map_sub, endpointJointRealFourierCoefficient_mixed,
    endpointJointRealFourierCoefficient_projection_mixed hT, h k c, sub_self]

end

end TorusEuler
