import TorusEuler.FreezingOperatorBounds
import TorusEuler.PeriodicMultiplierBounds
import TorusEuler.EndpointDensity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open ContinuousLinearMap MeasureTheory Set
open scoped InnerProductSpace ContDiff

namespace TorusEuler

local notation "SpatialOperator" => (Vec3 →L[ℝ] Vec3)
local notation "Punctured" => ({0}ᶜ : Set Vec3)

/-- The Leray projection at a real spatial frequency, with identity at zero. -/
noncomputable def angularLeray (ξ : Vec3) : SpatialOperator :=
  1 - InnerProductSpace.rankOne ℝ (NormedSpace.normalize ξ) (NormedSpace.normalize ξ)

@[simp] theorem angularLeray_zero : angularLeray 0 = 1 := by
  simp [angularLeray]

theorem angularLeray_apply (ξ v : Vec3) :
    angularLeray ξ v = v - (⟪ξ, v⟫_ℝ / ‖ξ‖ ^ 2) • ξ := by
  simp only [angularLeray, sub_apply, InnerProductSpace.rankOne_apply,
    NormedSpace.normalize, real_inner_smul_left, smul_smul]
  have h : ‖ξ‖⁻¹ * ⟪ξ, v⟫_ℝ * ‖ξ‖⁻¹ = ⟪ξ, v⟫_ℝ / ‖ξ‖ ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  rw [h]
  rfl

theorem angularLeray_isSymmetricProjection (ξ : Vec3) :
    (angularLeray ξ : Vec3 →ₗ[ℝ] Vec3).IsSymmetricProjection := by
  by_cases hξ : ξ = 0
  · subst ξ
    simpa only [angularLeray_zero] using
      (IsStarProjection.one SpatialOperator).isSymmetricProjection
  · exact
      (InnerProductSpace.isStarProjection_rankOne_self (NormedSpace.norm_normalize hξ)).one_sub
        |>.isSymmetricProjection

theorem norm_angularLeray_le (ξ : Vec3) : ‖angularLeray ξ‖ ≤ 1 :=
  (angularLeray_isSymmetricProjection ξ).isStarProjection.norm_le

theorem angularLeray_pos_smul {c : ℝ} (hc : 0 < c) (ξ : Vec3) :
    angularLeray (c • ξ) = angularLeray ξ := by
  simp [angularLeray, NormedSpace.normalize_smul_of_pos hc]

@[simp] theorem angularLeray_neg (ξ : Vec3) : angularLeray (-ξ) = angularLeray ξ := by
  ext v : 1
  simp [angularLeray_apply, neg_div]

theorem contDiffOn_angularLeray {n : ℕ∞ω} : ContDiffOn ℝ n angularLeray Punctured := by
  have hnorm : ContDiffOn ℝ n (fun x : Vec3 => ‖x‖) Punctured :=
    fun x hx => (contDiffAt_norm ℝ (by simpa using hx)).contDiffWithinAt
  have hnormalize : ContDiffOn ℝ n (NormedSpace.normalize : Vec3 → Vec3) Punctured := by
    unfold NormedSpace.normalize
    exact (hnorm.inv fun x hx => norm_ne_zero_iff.mpr (by simpa using hx)).smul contDiffOn_id
  let rankOne : Vec3 →L[ℝ] Vec3 →L[ℝ] SpatialOperator := InnerProductSpace.rankOne ℝ
  have houter : ContDiff ℝ n (⇑rankOne) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Vec3) (F := Vec3 →L[ℝ] SpatialOperator) rankOne
  have hcomp := houter.comp_contDiffOn hnormalize
  have hdiag := hcomp.clm_apply hnormalize
  have hconst : ContDiffOn ℝ n (fun _ : Vec3 => (1 : SpatialOperator)) Punctured :=
    contDiffOn_const
  exact hconst.sub hdiag

private theorem angularLeray_contDiffAt {n : ℕ∞ω} {ξ : Vec3} (hξ : ξ ≠ 0) :
    ContDiffAt ℝ n angularLeray ξ :=
  contDiffOn_angularLeray.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hξ))

/-- Positive rescaling of the frequency scales the order-`n` derivative by degree `-n`. -/
theorem iteratedFDeriv_angularLeray_pos_smul (n : ℕ) {c : ℝ} (hc : 0 < c)
    {ξ : Vec3} (hξ : ξ ≠ 0) :
    iteratedFDeriv ℝ n angularLeray ξ =
      c ^ n • iteratedFDeriv ℝ n angularLeray (c • ξ) := by
  let L : SpatialOperator := c • ContinuousLinearMap.id ℝ Vec3
  have hL (x : Vec3) : L x = c • x := rfl
  have hpreimage : L ⁻¹' Punctured = Punctured := by
    ext x
    simp [hL, smul_eq_zero, hc.ne']
  have hcomp : angularLeray ∘ L = angularLeray := by
    funext x
    exact angularLeray_pos_smul hc x
  have hmem : L ξ ∈ Punctured := by
    simp [hL, smul_eq_zero, hc.ne', hξ]
  have hpreUnique : UniqueDiffOn ℝ (L ⁻¹' Punctured) := by
    rw [hpreimage]
    exact isOpen_compl_singleton.uniqueDiffOn
  have h := L.iteratedFDerivWithin_comp_right (n := n) contDiffOn_angularLeray
    isOpen_compl_singleton.uniqueDiffOn hpreUnique hmem le_rfl
  rw [hpreimage, hcomp, hL] at h
  rw [iteratedFDerivWithin_eq_iteratedFDeriv isOpen_compl_singleton.uniqueDiffOn
      (angularLeray_contDiffAt hξ) (by simpa using hξ),
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_compl_singleton.uniqueDiffOn
      (angularLeray_contDiffAt (smul_ne_zero hc.ne' hξ))
      (by simpa only [mem_compl_iff, mem_singleton_iff] using smul_ne_zero hc.ne' hξ)] at h
  rw [h]
  ext v : 1
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hL, _root_.smul_apply]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ n angularLeray (c • ξ)).map_smul_univ (fun _ => c) v

private theorem exists_norm_iteratedFDeriv_angularLeray_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ n angularLeray ξ‖ ≤ C / ‖ξ‖ ^ n := by
  have hcont : ContinuousOn (fun ξ => iteratedFDeriv ℝ n angularLeray ξ) Punctured := by
    refine ((contDiffOn_angularLeray (n := n)).continuousOn_iteratedFDerivWithin (m := n)
      le_rfl isOpen_compl_singleton.uniqueDiffOn).congr ?_
    intro x hx
    exact (iteratedFDerivWithin_eq_iteratedFDeriv isOpen_compl_singleton.uniqueDiffOn
      (angularLeray_contDiffAt (by simpa using hx)) hx).symm
  have hsphere : Metric.sphere (0 : Vec3) 1 ⊆ Punctured := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
    simp [norm_ne_zero_iff.mp (hxnorm.symm ▸ one_ne_zero)]
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Vec3) 1).bddAbove_image (hcont.norm.mono hsphere)
  refine ⟨max 0 C, le_max_left _ _, fun ξ hξ => ?_⟩
  let e := NormedSpace.normalize ξ
  have he1 : ‖e‖ = 1 := NormedSpace.norm_normalize hξ
  have he : e ≠ 0 := norm_ne_zero_iff.mp (he1.symm ▸ one_ne_zero)
  have hesphere : e ∈ Metric.sphere (0 : Vec3) 1 := by simpa [dist_zero_right] using he1
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hξe : ‖ξ‖ • e = ξ := NormedSpace.norm_smul_normalize ξ
  have hscaling := iteratedFDeriv_angularLeray_pos_smul n hnorm he
  rw [hξe] at hscaling
  have hbound : ‖iteratedFDeriv ℝ n angularLeray e‖ ≤ max 0 C :=
    (hC ⟨e, hesphere, rfl⟩).trans (le_max_right _ _)
  apply (le_div_iff₀ (pow_pos hnorm n)).mpr
  rw [mul_comm, ← abs_of_nonneg (pow_nonneg hnorm.le n), ← Real.norm_eq_abs,
    ← norm_smul, ← hscaling]
  exact hbound

/-- The spatial Leray symbol has a uniform quantitative bound through each fixed derivative order. -/
theorem exists_angularLeray_jet_bound (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ ξ : Vec3, ξ ≠ 0 → ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i angularLeray ξ‖ ≤ (D / ‖ξ‖) ^ i := by
  choose C hC hbound using exists_norm_iteratedFDeriv_angularLeray_le
  let D : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), C i
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (n + 1)) => hC i)]
  refine ⟨D, hD, fun ξ hξ i hi => ?_⟩
  by_cases hi0 : i = 0
  · subst i
    simpa only [norm_iteratedFDeriv_zero, pow_zero] using norm_angularLeray_le ξ
  have hCD : C i ≤ D := by
    have hs := Finset.single_le_sum (f := C) (fun j _ => hC j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    dsimp only [D]
    linarith
  have hCDi : C i ≤ D ^ i := hCD.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hD (Nat.one_le_iff_ne_zero.mpr hi0))
  rw [div_pow]
  exact (hbound i ξ hξ).trans (div_le_div_of_nonneg_right hCDi (by positivity))

/-- An integer Fourier frequency viewed as a vector of real Euclidean coordinates. -/
def realFourierFrequency (k : Fin 3 → ℤ) : Vec3 := WithLp.toLp 2 (fun i => (k i : ℝ))

private theorem realFourierFrequency_norm_sq (k : Fin 3 → ℤ) :
    ‖realFourierFrequency k‖ ^ 2 = frequencyNormSq k := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

private theorem realFourierFrequency_inner (k : Fin 3 → ℤ) (v : Vec3) :
    ⟪realFourierFrequency k, v⟫_ℝ = ∑ i, (k i : ℝ) * v.ofLp i := by
  rw [PiLp.inner_apply]
  simp [realFourierFrequency, RCLike.inner_apply, mul_comm]

/-- Restriction of the complex Fourier symbol to real coefficients agrees
with the real angular symbol sampled on the integer lattice. -/
theorem lerayMode_ofRealVector (k : Fin 3 → ℤ) (v : Vec3) :
    lerayMode k (fun i => (v.ofLp i : ℂ)) =
      fun i => ((angularLeray (realFourierFrequency k) v).ofLp i : ℂ) := by
  funext i
  rw [angularLeray_apply, realFourierFrequency_norm_sq, realFourierFrequency_inner]
  simp [lerayMode, frequencyContraction, complexFrequency, realFourierFrequency]

/-- On arbitrary complex mode coefficients the real angular symbol acts
separately on the real and imaginary coordinate vectors. -/
theorem lerayMode_eq_angularLeray_complex_parts (k : Fin 3 → ℤ) (a : ComplexVec3) :
    let u : Vec3 := WithLp.toLp 2 (fun i => (a i).re)
    let v : Vec3 := WithLp.toLp 2 (fun i => (a i).im)
    lerayMode k a = fun i =>
      ((angularLeray (realFourierFrequency k) u).ofLp i : ℂ) +
        Complex.I * ((angularLeray (realFourierFrequency k) v).ofLp i : ℂ) := by
  intro u v
  have hsplit (i : Fin 3) : a i = (u.ofLp i : ℂ) + Complex.I * (v.ofLp i : ℂ) := by
    change a i = ((a i).re : ℂ) + Complex.I * ((a i).im : ℂ)
    simpa only [mul_comm Complex.I] using (Complex.re_add_im (a i)).symm
  have hcontraction : frequencyContraction k a =
      frequencyContraction k (fun i => (u.ofLp i : ℂ)) +
        Complex.I * frequencyContraction k (fun i => (v.ofLp i : ℂ)) := by
    simp only [frequencyContraction]
    simp_rw [hsplit, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  funext i
  rw [← congrFun (lerayMode_ofRealVector k u) i, ← congrFun (lerayMode_ofRealVector k v) i]
  simp only [lerayMode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hcontraction]
  rw [hsplit i]
  ring

section TimePaths

local notation "TimeMeasure(" T ")" => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (TimeMeasure(T))
local notation "PathOperator(" T ")" => (Paths(T) →L[ℝ] Paths(T))

/-- A constant spatial operator acts on time paths almost everywhere, and this
lifting is a bounded linear map between the spaces of operators. -/
noncomputable def spatialTimeLift (T : ℝ) : SpatialOperator →L[ℝ] PathOperator(T) :=
  (ContinuousLinearMap.id ℝ SpatialOperator).compLpL₂ 2 (TimeMeasure(T))

theorem spatialTimeLift_apply_ae (T : ℝ) (A : SpatialOperator) (v : Paths(T)) :
    ⇑(spatialTimeLift T A v) =ᵐ[TimeMeasure(T)] fun t => A (v t) :=
  A.coeFn_compLpL v

theorem norm_spatialTimeLift_le (T : ℝ) : ‖spatialTimeLift T‖ ≤ 1 :=
  (norm_compLpL₂_le (p := 2) (μ := TimeMeasure(T)) (ContinuousLinearMap.id ℝ SpatialOperator)).trans
    ContinuousLinearMap.norm_id_le

private theorem spatialTimeLift_integral (T : ℝ) (A : SpatialOperator) (v : Paths(T)) :
    endpointIntegral T (spatialTimeLift T A v) = A (endpointIntegral T v) := by
  simp only [endpointIntegral_apply]
  rw [integral_congr_ae (spatialTimeLift_apply_ae T A v)]
  exact A.integral_comp_comm ((Lp.memLp v).integrable (by norm_num))

private theorem spatialTimeLift_const (T : ℝ) (A : SpatialOperator) (c : Vec3) :
    spatialTimeLift T A (Lp.const 2 (TimeMeasure(T)) c) =
      Lp.const 2 (TimeMeasure(T)) (A c) := by
  apply Lp.ext
  filter_upwards [spatialTimeLift_apply_ae T A (Lp.const 2 (TimeMeasure(T)) c),
    Lp.coeFn_const 2 (TimeMeasure(T)) c, Lp.coeFn_const 2 (TimeMeasure(T)) (A c)]
    with t ht hc hAc
  exact ht.trans ((congrArg A hc).trans hAc.symm)

theorem spatialTimeLift_isSymmetricProjection (T : ℝ) {A : SpatialOperator}
    (hA : (A : Vec3 →ₗ[ℝ] Vec3).IsSymmetricProjection) :
    (spatialTimeLift T A : Paths(T) →ₗ[ℝ] Paths(T)).IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    intro v
    change spatialTimeLift T A (spatialTimeLift T A v) = spatialTimeLift T A v
    apply Lp.ext
    filter_upwards [spatialTimeLift_apply_ae T A (spatialTimeLift T A v),
      spatialTimeLift_apply_ae T A v] with t ht hv
    rw [ht, hv]
    exact DFunLike.congr_fun hA.isIdempotentElem (v t)
  · intro v w
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [spatialTimeLift_apply_ae T A v, spatialTimeLift_apply_ae T A w]
      with t hv hw
    change ⟪spatialTimeLift T A v t, w t⟫_ℝ = ⟪v t, spatialTimeLift T A w t⟫_ℝ
    rw [hv, hw]
    exact hA.isSymmetric (v t) (w t)

private theorem inner_path_const_left (T : ℝ) (c : Vec3) (v : Paths(T)) :
    ⟪Lp.const 2 (TimeMeasure(T)) c, v⟫_ℝ = ⟪c, endpointIntegral T v⟫_ℝ := by
  rw [L2.inner_def, endpointIntegral_apply]
  have h : (fun t => ⟪Lp.const 2 (TimeMeasure(T)) c t, v t⟫_ℝ) =ᵐ[TimeMeasure(T)]
      fun t => ⟪c, v t⟫_ℝ := by
    filter_upwards [Lp.coeFn_const 2 (TimeMeasure(T)) c] with t ht
    rw [ht]
    rfl
  rw [integral_congr_ae h]
  exact (innerSL ℝ c).integral_comp_comm ((Lp.memLp v).integrable (by norm_num))

theorem endpointSubtractMean_isSymmetricProjection {T : ℝ} (hT : 0 < T) :
    ((endpointSubtractMean (E := Vec3) T : PathOperator(T)) :
      Paths(T) →ₗ[ℝ] Paths(T)).IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    intro v
    change endpointSubtractMean T (endpointSubtractMean T v) = endpointSubtractMean T v
    rw [endpointSubtractMean_apply, endpointIntegral_subtractMean hT]
    simp
  · intro v w
    change ⟪endpointSubtractMean T v, w⟫_ℝ = ⟪v, endpointSubtractMean T w⟫_ℝ
    have hright : ⟪v, Lp.const 2 (TimeMeasure(T)) (T⁻¹ • endpointIntegral T w)⟫_ℝ =
        ⟪T⁻¹ • endpointIntegral T w, endpointIntegral T v⟫_ℝ :=
      (real_inner_comm _ _).trans (inner_path_const_left T _ v)
    rw [endpointSubtractMean_apply T v, endpointSubtractMean_apply T w, inner_sub_left,
      inner_sub_right, inner_path_const_left, hright,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_comm (endpointIntegral T v) (endpointIntegral T w)]

theorem spatialTimeLift_commutes_endpointSubtractMean (T : ℝ) (A : SpatialOperator) :
    Commute (spatialTimeLift T A) (endpointSubtractMean T : PathOperator(T)) := by
  apply ContinuousLinearMap.ext
  intro v
  change spatialTimeLift T A (endpointSubtractMean T v) =
    endpointSubtractMean T (spatialTimeLift T A v)
  rw [endpointSubtractMean_apply T v, endpointSubtractMean_apply T (spatialTimeLift T A v),
    map_sub, spatialTimeLift_const, spatialTimeLift_integral, map_smul]

/-- The symbol for a spatially solenoidal and temporally mean-zero path. -/
noncomputable def angularTimeLeray (T : ℝ) (ξ : Vec3) : PathOperator(T) :=
  spatialTimeLift T (angularLeray ξ) * endpointSubtractMean T

theorem angularTimeLeray_apply_ae (T : ℝ) (ξ : Vec3) (v : Paths(T)) :
    ⇑(angularTimeLeray T ξ v) =ᵐ[TimeMeasure(T)]
      fun t => angularLeray ξ (endpointSubtractMean T v t) :=
  spatialTimeLift_apply_ae T (angularLeray ξ) (endpointSubtractMean T v)

theorem endpointIntegral_angularTimeLeray {T : ℝ} (hT : 0 < T) (ξ : Vec3) (v : Paths(T)) :
    endpointIntegral T (angularTimeLeray T ξ v) = 0 := by
  change endpointIntegral T (spatialTimeLift T (angularLeray ξ) (endpointSubtractMean T v)) = 0
  rw [spatialTimeLift_integral, endpointIntegral_subtractMean hT, map_zero]

@[simp] theorem angularTimeLeray_zero (T : ℝ) :
    angularTimeLeray T 0 = endpointSubtractMean T := by
  have h : spatialTimeLift T (1 : SpatialOperator) = 1 := by
    ext1 v
    apply Lp.ext
    exact spatialTimeLift_apply_ae T 1 v
  rw [angularTimeLeray, angularLeray_zero, h, one_mul]

theorem angularTimeLeray_isSymmetricProjection {T : ℝ} (hT : 0 < T) (ξ : Vec3) :
    (angularTimeLeray T ξ : Paths(T) →ₗ[ℝ] Paths(T)).IsSymmetricProjection :=
  ((spatialTimeLift_isSymmetricProjection T (angularLeray_isSymmetricProjection ξ)).isStarProjection.mul
    (endpointSubtractMean_isSymmetricProjection hT).isStarProjection
    (spatialTimeLift_commutes_endpointSubtractMean T (angularLeray ξ))).isSymmetricProjection

private noncomputable def timeLerayLift (T : ℝ) : SpatialOperator →L[ℝ] PathOperator(T) :=
  ((mul ℝ (PathOperator(T))).flip (endpointSubtractMean T)).comp (spatialTimeLift T)

private theorem norm_timeLerayLift_le {T : ℝ} (hT : 0 < T) : ‖timeLerayLift T‖ ≤ 1 := by
  have hQ : ‖(endpointSubtractMean T : PathOperator(T))‖ ≤ 1 :=
    (endpointSubtractMean_isSymmetricProjection hT).isStarProjection.norm_le
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖spatialTimeLift T A * (endpointSubtractMean T : PathOperator(T))‖ ≤ 1 * ‖A‖
  rw [one_mul]
  calc
    _ ≤ ‖spatialTimeLift T A‖ * ‖(endpointSubtractMean T : PathOperator(T))‖ := norm_mul_le _ _
    _ ≤ ‖spatialTimeLift T A‖ := mul_le_of_le_one_right (norm_nonneg _) hQ
    _ ≤ ‖A‖ := (spatialTimeLift T).le_of_opNorm_le (norm_spatialTimeLift_le T) A |>.trans_eq
      (one_mul ‖A‖)

theorem angularTimeLeray_pos_smul (T : ℝ) {c : ℝ} (hc : 0 < c) (ξ : Vec3) :
    angularTimeLeray T (c • ξ) = angularTimeLeray T ξ := by
  rw [angularTimeLeray, angularLeray_pos_smul hc, angularTimeLeray]

theorem contDiffOn_angularTimeLeray (T : ℝ) {n : ℕ∞ω} :
    ContDiffOn ℝ n (angularTimeLeray T) Punctured :=
  (timeLerayLift T).contDiff.comp_contDiffOn contDiffOn_angularLeray

theorem norm_iteratedFDeriv_angularTimeLeray_le {T : ℝ} (hT : 0 < T)
    (i : ℕ) {ξ : Vec3} (hξ : ξ ≠ 0) :
    ‖iteratedFDeriv ℝ i (angularTimeLeray T) ξ‖ ≤ ‖iteratedFDeriv ℝ i angularLeray ξ‖ := by
  change ‖iteratedFDeriv ℝ i (timeLerayLift T ∘ angularLeray) ξ‖ ≤ _
  have h := (timeLerayLift T).norm_iteratedFDeriv_comp_left
    (angularLeray_contDiffAt (n := i) hξ) le_rfl
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) (norm_timeLerayLift_le hT))

/-- There is a bound depending only on the spatial order, uniform in the time length
and the two projected spatial symbols. -/
theorem exists_angularLeray_frozen_inverse_bounds (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧
      (∀ (B : SpatialOperator) {μ : ℝ}, 0 < μ →
        (∀ v, μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) →
        ∀ (ξ : Vec3), ξ ≠ 0 →
          ‖iteratedFDeriv ℝ n (fun η => Ring.inverse (frozenSymbol (angularLeray η) B)) ξ‖ ≤
            (n.factorial : ℝ) ^ 2 * ((min 1 μ)⁻¹) ^ (n + 1) *
              (2 * (D / ‖ξ‖) * (‖B‖ + 1)) ^ n) ∧
      (∀ {T : ℝ}, 0 < T → ∀ (B : PathOperator(T)) {μ : ℝ}, 0 < μ →
        (∀ v, endpointIntegral T v = 0 → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) →
        ∀ (ξ : Vec3), ξ ≠ 0 →
          ‖iteratedFDeriv ℝ n (fun η => Ring.inverse (frozenSymbol (angularTimeLeray T η) B)) ξ‖ ≤
            (n.factorial : ℝ) ^ 2 * ((min 1 μ)⁻¹) ^ (n + 1) *
              (2 * (D / ‖ξ‖) * (‖B‖ + 1)) ^ n) := by
  obtain ⟨D, hD, hjet⟩ := exists_angularLeray_jet_bound n
  have hdiv (ξ : Vec3) : 0 ≤ D / ‖ξ‖ := div_nonneg (zero_le_one.trans hD) (norm_nonneg _)
  refine ⟨D, hD, ?_, ?_⟩
  · intro B μ hμ hB ξ hξ
    exact norm_iteratedFDeriv_frozenSymbol_inverse_of_projection_bounds isOpen_compl_singleton
      hμ (fun η _ => angularLeray_isSymmetricProjection η) (fun _ _ v _ => hB v)
      (by simpa using hξ) contDiffOn_angularLeray (hdiv ξ) (hjet ξ hξ)
  · intro T hT B μ hμ hB ξ hξ
    have hcoeff (η : Vec3) (v : Paths(T)) (hv : angularTimeLeray T η v = v) :
        μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ :=
      hB v (hv ▸ endpointIntegral_angularTimeLeray hT η v)
    exact norm_iteratedFDeriv_frozenSymbol_inverse_of_projection_bounds isOpen_compl_singleton
      hμ (fun η _ => angularTimeLeray_isSymmetricProjection hT η) (fun η _ => hcoeff η)
      (by simpa using hξ) (contDiffOn_angularTimeLeray T) (hdiv ξ)
      (fun i hi => (norm_iteratedFDeriv_angularTimeLeray_le hT i hξ).trans (hjet ξ hξ i hi))

end TimePaths

end TorusEuler
