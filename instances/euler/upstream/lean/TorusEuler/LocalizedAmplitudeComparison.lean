import TorusEuler.FirstWaveInitialization
import TorusEuler.EulerLimitClosure
import TorusEuler.ActivationProfiles
import TorusEuler.InductionScales
import TorusEuler.WavePressureCenter
import Mathlib.Analysis.Real.Pi.Bounds
import TorusEuler.OscillatoryHierarchySolve
import TorusEuler.OscillatoryLabelRegularity
import TorusEuler.ParentCoframeEstimates
import TorusEuler.PhysicalGrowthPropagator

/-! Relative propagation of the localized seed in Lemma 5.5. -/

open ContinuousLinearMap Set MeasureTheory
open scoped ContDiff InnerProductSpace
open NormedSpace (normalize)

namespace TorusEuler

section LocalizedDuhamel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The weighted difference between solutions at a nearby label and at the
center is controlled by the initial difference and the coefficient change. -/
theorem weighted_near_label_difference_norm_le
    {A A₁ : ℝ → E →L[ℝ] E} {g dg : ℝ → ℝ} {x y : ℝ → E}
    {a b t K d : ℝ}
    (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : b - a ≤ 1) (hsmall : K * d ≤ 1)
    (hA : ContinuousOn A (Icc a b)) (hA₁ : ContinuousOn A₁ (Icc a b))
    (hchange : ∀ u ∈ Icc a b, ‖A₁ u - A u‖ ≤ d)
    (hg₀ : ∀ u ∈ Icc a b, 0 < g u)
    (hg : ∀ u ∈ Icc a b, HasDerivWithinAt g (dg u) (Icc a b) u)
    (hdg : ContinuousOn dg (Icc a b))
    (hCenter : ∀ z : ℝ → E,
      (∀ u ∈ Icc a b, HasDerivWithinAt z (A u (z u)) (Icc a b) u) →
      ∀ u ∈ Icc a b, ∀ v ∈ Icc u b, ‖z v‖ / g v ≤ K * (‖z u‖ / g u))
    (hx : ∀ u ∈ Icc a b, HasDerivWithinAt x (A₁ u (x u)) (Icc a b) u)
    (hy : ∀ u ∈ Icc a b, HasDerivWithinAt y (A u (y u)) (Icc a b) u)
    (ht : t ∈ Icc a b) :
    ‖x t - y t‖ / g t ≤ K * (‖x a - y a‖ / g a) +
      Real.exp 1 * K ^ 2 * (‖x a‖ / g a) * d := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hx' (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivWithinAt x (A u (x u) + (A₁ u - A u) (x u)) (Icc a b) u := by
    simpa only [sub_apply, add_sub_cancel] using hx u hu
  let D := ∫ u in a..t, (fun _ : ℝ => d) u
  have hDeq : D = (t - a) * d := by
    simp only [D, intervalIntegral.integral_const, smul_eq_mul]
  have hD₀ : 0 ≤ D := by
    rw [hDeq]
    exact mul_nonneg (sub_nonneg.mpr ht.1) hd
  have hD : D ≤ d := by
    rw [hDeq]
    exact mul_le_of_le_one_left hd ((sub_le_sub_right ht.2 a).trans hT)
  have hExp : Real.exp (K * D) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hD hK).trans hsmall)
  have h := (weighted_linearODE_perturbation_bounds hK hA (hA₁.sub hA)
    continuousOn_const hchange hg₀ hg hdg hCenter hx' hy ht).2
  have hbase : 0 ≤ K ^ 2 * (‖x a‖ / g a) :=
    mul_nonneg (sq_nonneg K) (div_nonneg (norm_nonneg _) (hg₀ a ha).le)
  refine h.trans (add_le_add_right ?_ _)
  calc
    K ^ 2 * (‖x a‖ / g a) * Real.exp (K * D) * D ≤
        K ^ 2 * (‖x a‖ / g a) * Real.exp 1 * d :=
      mul_le_mul (mul_le_mul_of_nonneg_left hExp hbase) hD hD₀
        (mul_nonneg hbase (Real.exp_nonneg _))
    _ = Real.exp 1 * K ^ 2 * (‖x a‖ / g a) * d := by ring

end LocalizedDuhamel

section NearLabelContraction

variable {E : Type*} [NormedAddCommGroup E]

/-- A relative perturbation of a vector controls both its lower and upper norm. -/
theorem localized_norm_bounds {x x₀ : E} {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hx : ‖x - x₀‖ ≤ δ * ‖x₀‖) :
    ‖x₀‖ / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * ‖x₀‖ := by
  have hdiff : ‖x - x₀‖ ≤ ‖x₀‖ / 2 := hx.trans (by
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hδ (norm_nonneg x₀))
  have hlow : ‖x₀‖ ≤ ‖x‖ + ‖x - x₀‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le x (x - x₀)
  have hupp : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - x₀) x₀
  constructor <;> linarith [norm_nonneg x₀]

variable [InnerProductSpace ℝ E]

/-- The moving-frame first coupling is the unnormalized contraction divided by
the product of the wave-vector and amplitude norms. -/
theorem localized_normalized_coupling_eq_div (k a : E) (M : E →L[ℝ] E) :
    ⟪NormedSpace.normalize k, M (NormedSpace.normalize a)⟫_ℝ =
      ⟪k, M a⟫_ℝ / (‖k‖ * ‖a‖) := by
  simp only [NormedSpace.normalize, map_smul, real_inner_smul_left, real_inner_smul_right,
    div_eq_mul_inv]
  ring

/-- The physical first-coupling contraction changes at most linearly under
relative changes of wave vector and amplitude and an absolute change of gradient. -/
theorem localized_couplingDifference_le {k k₀ a a₀ : E} {M M₀ : E →L[ℝ] E} {δ D : ℝ}
    (hD : 1 ≤ D) (hδ₀ : 0 ≤ δ) (hδ : δ ≤ 1) (hM : ‖M‖ ≤ D)
    (hk : ‖k - k₀‖ ≤ δ * ‖k₀‖) (ha : ‖a - a₀‖ ≤ δ * ‖a₀‖)
    (hMdiff : ‖M - M₀‖ ≤ δ) :
    |⟪k, M a⟫_ℝ - ⟪k₀, M₀ a₀⟫_ℝ| ≤ (4 * D * δ) * (‖k₀‖ * ‖a₀‖) := by
  have hDa : ‖a‖ ≤ 2 * ‖a₀‖ := by
    calc
      ‖a‖ ≤ ‖a - a₀‖ + ‖a₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (a - a₀) a₀
      _ ≤ δ * ‖a₀‖ + ‖a₀‖ := add_le_add ha le_rfl
      _ ≤ 2 * ‖a₀‖ := by
        linarith [mul_le_mul_of_nonneg_right hδ (norm_nonneg a₀)]
  have hMD (x : E) : ‖M x‖ ≤ D * ‖x‖ :=
    (M.le_opNorm x).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg x))
  have h₁ : |⟪k - k₀, M a⟫_ℝ| ≤ (δ * ‖k₀‖) * (D * (2 * ‖a₀‖)) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    apply mul_le_mul hk ((hMD a).trans (mul_le_mul_of_nonneg_left hDa (by linarith)))
      (norm_nonneg _) (by positivity)
  have h₂ : |⟪k₀, M (a - a₀)⟫_ℝ| ≤ ‖k₀‖ * (D * (δ * ‖a₀‖)) :=
    (abs_real_inner_le_norm _ _).trans <| mul_le_mul_of_nonneg_left
      ((hMD (a - a₀)).trans (mul_le_mul_of_nonneg_left ha (by linarith))) (norm_nonneg _)
  have h₃ : |⟪k₀, (M - M₀) a₀⟫_ℝ| ≤ ‖k₀‖ * (δ * ‖a₀‖) :=
    (abs_real_inner_le_norm _ _).trans <| mul_le_mul_of_nonneg_left
      (((M - M₀).le_opNorm a₀).trans (mul_le_mul_of_nonneg_right hMdiff (norm_nonneg _)))
      (norm_nonneg _)
  have hsplit : ⟪k, M a⟫_ℝ - ⟪k₀, M₀ a₀⟫_ℝ =
      ⟪k - k₀, M a⟫_ℝ + ⟪k₀, M (a - a₀)⟫_ℝ + ⟪k₀, (M - M₀) a₀⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right, map_sub, sub_apply]
    ring
  calc
    _ ≤ |⟪k - k₀, M a⟫_ℝ| + |⟪k₀, M (a - a₀)⟫_ℝ| + |⟪k₀, (M - M₀) a₀⟫_ℝ| := by
      rw [hsplit]
      exact (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
    _ ≤ (δ * ‖k₀‖) * (D * (2 * ‖a₀‖)) + ‖k₀‖ * (D * (δ * ‖a₀‖)) +
        ‖k₀‖ * (δ * ‖a₀‖) := add_le_add (add_le_add h₁ h₂) h₃
    _ = ((3 * D + 1) * δ) * (‖k₀‖ * ‖a₀‖) := by ring
    _ ≤ _ := by gcongr; linarith

/-- The central coupling lower bound survives nearby label perturbations.
Besides the strict sign in (5.22), this gives the comparison of the wave-vector
and seed norms and a quantitative normalized coupling lower bound. -/
theorem localized_coupling_positive {k k₀ a a₀ : E} {M M₀ : E →L[ℝ] E} {δ D : ℝ}
    (hD : 1 ≤ D) (hδ₀ : 0 ≤ δ) (hδ : δ ≤ (8 * D ^ 2)⁻¹) (hM : ‖M‖ ≤ D)
    (hk₀ : 0 < ‖k₀‖) (ha₀ : 0 < ‖a₀‖)
    (hk : ‖k - k₀‖ ≤ δ * ‖k₀‖) (ha : ‖a - a₀‖ ≤ δ * ‖a₀‖)
    (hMdiff : ‖M - M₀‖ ≤ δ)
    (hcenter : D⁻¹ * (‖k₀‖ * ‖a₀‖) ≤ ⟪k₀, M₀ a₀⟫_ℝ) :
    (‖a₀‖ / 2 ≤ ‖a‖ ∧ ‖a‖ ≤ 2 * ‖a₀‖) ∧
    (‖k₀‖ / 2 ≤ ‖k‖ ∧ ‖k‖ ≤ 2 * ‖k₀‖) ∧
    (2 * D)⁻¹ * (‖k₀‖ * ‖a₀‖) ≤ ⟪k, M a⟫_ℝ ∧
    0 < ⟪k, M a⟫_ℝ ∧
    (8 * D)⁻¹ ≤ ⟪k, M a⟫_ℝ / (‖k‖ * ‖a‖) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hDsq : 1 ≤ D ^ 2 := one_le_pow₀ hD
  have hδ' : δ ≤ 1 / 2 :=
    hδ.trans (by
      rw [one_div]
      exact inv_anti₀ (show (0 : ℝ) < 2 by norm_num)
        (show (2 : ℝ) ≤ 8 * D ^ 2 by linarith))
  have haNorm := localized_norm_bounds hδ' ha
  have hkNorm := localized_norm_bounds hδ' hk
  have hcoeff : (4 * D * δ) ≤ (2 * D)⁻¹ := by
    calc
      _ ≤ 4 * D * (8 * D ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = _ := by field_simp; ring
  have herr := (localized_couplingDifference_le hD hδ₀
    (hδ'.trans (by norm_num)) hM hk ha hMdiff).trans
      (mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ ‖k₀‖ * ‖a₀‖))
  have hhalf : (2 * D)⁻¹ + (2 * D)⁻¹ = D⁻¹ := by field_simp; ring
  have hraw : (2 * D)⁻¹ * (‖k₀‖ * ‖a₀‖) ≤ ⟪k, M a⟫_ℝ := by
    have heq : (2 * D)⁻¹ * (‖k₀‖ * ‖a₀‖) + (2 * D)⁻¹ * (‖k₀‖ * ‖a₀‖) =
        D⁻¹ * (‖k₀‖ * ‖a₀‖) := by rw [← add_mul, hhalf]
    linarith only [neg_abs_le (⟪k, M a⟫_ℝ - ⟪k₀, M₀ a₀⟫_ℝ), herr, heq, hcenter]
  have hkpos : 0 < ‖k‖ := (half_pos hk₀).trans_le hkNorm.1
  have hapos : 0 < ‖a‖ := (half_pos ha₀).trans_le haNorm.1
  refine ⟨haNorm, hkNorm, hraw, (by positivity : 0 < (2 * D)⁻¹ * (‖k₀‖ * ‖a₀‖)).trans_le hraw,
    (le_div_iff₀ (mul_pos hkpos hapos)).2 ?_⟩
  calc
    _ ≤ (8 * D)⁻¹ * ((2 * ‖k₀‖) * (2 * ‖a₀‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hkNorm.2 haNorm.2 hapos.le (by positivity)) (by positivity)
    _ = (2 * D)⁻¹ * (‖k₀‖ * ‖a₀‖) := by field_simp; ring
    _ ≤ _ := hraw

end NearLabelContraction

section FixedTransverse

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The homogeneous operator of the seed equation in fixed transverse
coordinates. The map `R` projects onto the moving transverse plane and
then reads its coordinates. -/
noncomputable def fixedTransverseGenerator (M : E →L[ℝ] E) (J : S →L[ℝ] E)
    (R : E →L[ℝ] S) : S →L[ℝ] S :=
  (-2 : ℝ) • R.comp (M.comp J)

theorem continuousOn_fixedTransverseGenerator
    {M : ℝ → E →L[ℝ] E} {J : ℝ → S →L[ℝ] E} {R : ℝ → E →L[ℝ] S}
    {I : Set ℝ} (hM : ContinuousOn M I) (hJ : ContinuousOn J I) (hR : ContinuousOn R I) :
    ContinuousOn (fun t => fixedTransverseGenerator (M t) (J t) (R t)) I :=
  (continuousOn_const (c := (-2 : ℝ))).smul (hR.clm_comp (hM.clm_comp hJ))

/-- The two coordinate identities identify the image of the lift as a
subspace of the moving transverse plane. -/
theorem inner_fixedTransverse_lift_eq_zero {k : E} (hk : k ≠ 0)
    {J : S →L[ℝ] E} {R : E →L[ℝ] S}
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ S)
    (hJR : J.comp R = oscillatoryTransverseProjection k) (z : S) :
    ⟪k, J z⟫_ℝ = 0 := by
  have hLeft : R (J z) = z := DFunLike.congr_fun hRJ z
  have hRight : J (R (J z)) = oscillatoryTransverseProjection k (J z) :=
    DFunLike.congr_fun hJR (J z)
  rw [hLeft] at hRight
  rw [hRight]
  exact inner_oscillatoryTransverseProjection k (J z) hk

/-- Reading the projected initial seed is the same as reading the original
vector, because the reader already includes transverse projection. -/
theorem fixedTransverse_read_projection {k : E} {J : S →L[ℝ] E} {R : E →L[ℝ] S}
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ S)
    (hJR : J.comp R = oscillatoryTransverseProjection k) (z : E) :
    R (oscillatoryTransverseProjection k z) = R z := by
  rw [← hJR]
  exact DFunLike.congr_fun hRJ (R z)

/-- A solution of the fixed-coordinate seed equation lifts to an actual
physical amplitude solution. Only the forward lift is differentiated. -/
theorem hasDerivWithinAt_fixedTransverse_lift
    {M : E →L[ℝ] E} {k : E} {J : ℝ → S →L[ℝ] E} {R : E →L[ℝ] S}
    {x : ℝ → S} {I : Set ℝ} {t : ℝ}
    (hJR : (J t).comp R = oscillatoryTransverseProjection k)
    (hJ : HasDerivWithinAt J (M.comp (J t)) I t)
    (hx : HasDerivWithinAt x (fixedTransverseGenerator M (J t) R (x t)) I t) :
    HasDerivWithinAt (fun q => J q (x q))
      (affineWaveAmplitudeOperator M k (J t (x t))) I t := by
  refine (hJ.clm_apply hx).congr_deriv ?_
  let z := M (J t (x t))
  have hRight : J t (R z) = oscillatoryTransverseProjection k z :=
    DFunLike.congr_fun hJR z
  change z + J t ((-2 : ℝ) • R z) = affineWaveAmplitudeOperator M k (J t (x t))
  rw [map_smul, hRight, affineWaveAmplitudeOperator_apply,
    oscillatoryTransverseProjection_apply]
  change z + (-2 : ℝ) • (z - (⟪k, z⟫_ℝ / ‖k‖ ^ 2) • k) =
    -z + (2 * ⟪k, z⟫_ℝ / ‖k‖ ^ 2) • k
  module

/-- The physical center growth estimate gives the fixed-coordinate estimate
on the same slab. Reading and lifting coordinates cost the two deformation
bounds, so a physical constant `D` becomes `D^3` when both are at most `D`. -/
theorem weighted_fixedTransverse_forward
    {M : ℝ → E →L[ℝ] E} {k : ℝ → E}
    {J : ℝ → S →L[ℝ] E} {R : ℝ → E →L[ℝ] S} {g : ℝ → ℝ}
    {I : Set ℝ} {K DJ DR : ℝ}
    (hK : 0 ≤ K) (hDR : 0 ≤ DR)
    (hk : ∀ t ∈ I, k t ≠ 0) (hg : ∀ t ∈ I, 0 < g t)
    (hRJ : ∀ t ∈ I, (R t).comp (J t) = ContinuousLinearMap.id ℝ S)
    (hJR : ∀ t ∈ I, (J t).comp (R t) = oscillatoryTransverseProjection (k t))
    (hJ : ∀ t ∈ I, HasDerivWithinAt J ((M t).comp (J t)) I t)
    (hJnorm : ∀ t ∈ I, ‖J t‖ ≤ DJ) (hRnorm : ∀ t ∈ I, ‖R t‖ ≤ DR)
    (hCenter : ∀ b : ℝ → E,
      (∀ t ∈ I, HasDerivWithinAt b
        (affineWaveAmplitudeOperator (M t) (k t) (b t)) I t) →
      (∀ t ∈ I, ⟪k t, b t⟫_ℝ = 0) →
      ∀ {u v : ℝ}, u ∈ I → v ∈ I → u ≤ v →
        ‖b v‖ / g v ≤ K * (‖b u‖ / g u))
    (x : ℝ → S)
    (hx : ∀ t ∈ I, HasDerivWithinAt x
      (fixedTransverseGenerator (M t) (J t) (R t) (x t)) I t)
    {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I) (huv : u ≤ v) :
    ‖x v‖ / g v ≤ (DR * K * DJ) * (‖x u‖ / g u) := by
  let b (t : ℝ) := J t (x t)
  have hLift (t : ℝ) (ht : t ∈ I) :
      HasDerivWithinAt b (affineWaveAmplitudeOperator (M t) (k t) (b t)) I t :=
    hasDerivWithinAt_fixedTransverse_lift (hJR t ht) (hJ t ht) (hx t ht)
  have hPerp (t : ℝ) (ht : t ∈ I) : ⟪k t, b t⟫_ℝ = 0 :=
    inner_fixedTransverse_lift_eq_zero (hk t ht) (hRJ t ht) (hJR t ht) (x t)
  have hNormU : ‖b u‖ ≤ DJ * ‖x u‖ := (J u).le_of_opNorm_le (hJnorm u hu) (x u)
  have hEqV : R v (b v) = x v := DFunLike.congr_fun (hRJ v hv) (x v)
  have hNormV : ‖x v‖ ≤ DR * ‖b v‖ := by
    rw [← hEqV]
    exact (R v).le_of_opNorm_le (hRnorm v hv) (b v)
  have hU : ‖b u‖ / g u ≤ DJ * (‖x u‖ / g u) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hNormU (hg u hu).le
  calc
    _ ≤ DR * (‖b v‖ / g v) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hNormV (hg v hv).le
    _ ≤ DR * (K * (‖b u‖ / g u)) :=
      mul_le_mul_of_nonneg_left (hCenter b hLift hPerp hu hv huv) hDR
    _ ≤ DR * (K * (DJ * (‖x u‖ / g u))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU hK) hDR
    _ = _ := by ring

end FixedTransverse

open NormedSpace (normalize)
open MovingWaveVector

private theorem raw_center_coupling_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) {k a : E} {D : ℝ} (hk : k ≠ 0) (ha : a ≠ 0)
    (h : D⁻¹ ≤ ⟪normalize k, M (normalize a)⟫_ℝ) :
    D⁻¹ * (‖k‖ * ‖a‖) ≤ ⟪k, M a⟫_ℝ := by
  have hmul : ⟪normalize k, M (normalize a)⟫_ℝ * (‖k‖ * ‖a‖) = ⟪k, M a⟫_ℝ := by
    rw [NormedSpace.normalize, NormedSpace.normalize, map_smul, real_inner_smul_left,
      real_inner_smul_right]
    field_simp [norm_ne_zero_iff.mpr hk, norm_ne_zero_iff.mpr ha]
  exact (mul_le_mul_of_nonneg_right h (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq hmul

/-- The first central wave supplies homogeneous growth and the raw first
coupling margin used to prove (5.22). -/
theorem FirstWaveOrigin.localized_center_estimates {s T freq D : ℝ} (w : FirstWaveOrigin s T freq)
    (hf : 0 < freq) (hs : |s| ≤ 1)
    (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) (hD : 2 ≤ D) :
    (∀ (b : ℝ → Vec3),
      (∀ t ∈ Icc 0 T, HasDerivWithinAt b
        (affineWaveAmplitudeOperator (stationaryShearGradient s) (w.covector t) (b t)) (Icc 0 T) t) →
      ∀ {u v : ℝ}, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
        ‖b v‖ / ‖w.amplitude v‖ ≤ D * (‖b u‖ / ‖w.amplitude u‖)) ∧
      ∀ t ∈ Icc 0 T,
        D⁻¹ * (‖w.covector t‖ * ‖w.amplitude t‖) ≤
          ⟪w.covector t, stationaryShearGradient s (w.amplitude t)⟫_ℝ := by
  constructor
  · intro b hb u v hu hv huv
    let L := freq ^ (3 / 4 : ℝ)
    have hL : 0 < L := Real.rpow_pos_of_pos hf _
    have h := w.weighted_forward hf hsmall hD hu hv huv hb
    change ‖b v‖ / (L * ‖w.amplitude v‖) ≤ D * (‖b u‖ / (L * ‖w.amplitude u‖)) at h
    have hcancel (t : ℝ) : L * (‖b t‖ / (L * ‖w.amplitude t‖)) =
        ‖b t‖ / ‖w.amplitude t‖ := by
      rw [div_mul_eq_div_div_swap, mul_div_cancel₀ _ hL.ne']
    have hscaled := mul_le_mul_of_nonneg_left h hL.le
    rw [hcancel v, mul_left_comm L D, hcancel u] at hscaled
    exact hscaled
  · intro t ht
    have hπ : Real.pi ≤
        ⟪normalize (w.covector t), stationaryShearGradient s (normalize (w.amplitude t))⟫_ℝ := by
      simpa only [entry, frame, Matrix.cons_val_zero, Matrix.cons_val_one]
        using w.first_coupling_lower hf hs hsmall ht
    have hDπ : D⁻¹ ≤ Real.pi := by
      calc
        _ ≤ 1 := (inv_le_one₀ (by linarith : 0 < D)).mpr (by linarith)
        _ ≤ _ := by linarith only [Real.pi_gt_three]
    exact raw_center_coupling_lower _ (w.transverse t ht).1 (w.transverse t ht).2.1
      (hDπ.trans hπ)

namespace MovingWaveVector.PhysicalAmplification

/-- The later central wave supplies the corresponding growth and raw coupling
on the very same physical trajectory as its crossing. -/
theorem exists_localized_center_estimates_threshold :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
        ∀ (w : PhysicalAmplification I t₀) (d : w.GrowingCrossing T scale Ustar next),
          2 ≤ T → scale ≠ 0 → (C₀ : ℝ) * w.ratio ≤ 1 →
          (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
          ∀ D : ℝ, 252 * Real.exp 1 * w.shear ≤ D → 2 / (w.firstCoupling * w.ratio) ≤ D →
            (∀ (b : ℝ → Space),
              (∀ t ∈ w.activeSlab T, HasDerivWithinAt b
                (affineWaveAmplitudeOperator (w.gradient t) (d.waveVector t) (b t))
                (w.activeSlab T) t) →
              (∀ t ∈ w.activeSlab T, ⟪d.waveVector t, b t⟫_ℝ = 0) →
              ∀ {u v : ℝ}, u ∈ w.activeSlab T → v ∈ w.activeSlab T → u ≤ v →
                ‖b v‖ / ‖d.amplitude v‖ ≤ D * (‖b u‖ / ‖d.amplitude u‖)) ∧
              ∀ t ∈ w.activeSlab T,
                D⁻¹ * (‖d.waveVector t‖ * ‖d.amplitude t‖) ≤
                  ⟪d.waveVector t, w.gradient t (d.amplitude t)⟫_ℝ := by
  obtain ⟨N, hN, hgrowth⟩ := exists_physical_growth_bound_threshold
  refine ⟨N, hN, ?_⟩
  intro I t₀ T scale Ustar next C₀ hNC w d hT hscale hε hδ D hDgrowth hDν
  constructor
  · intro b hb hp u v hu hv huv
    exact (hgrowth hNC w d hT hscale hε hδ b hb hp hu hv huv).trans
      (mul_le_mul_of_nonneg_right hDgrowth (div_nonneg (norm_nonneg _) (norm_nonneg _)))
  · intro t ht
    have hbase : 0 < w.firstCoupling * w.ratio / 2 :=
      half_pos (mul_pos w.first_coupling_positive w.ratio_pos)
    have hInv : (w.firstCoupling * w.ratio / 2)⁻¹ = 2 / (w.firstCoupling * w.ratio) :=
      inv_div _ _
    have h := inv_anti₀ (inv_pos.mpr hbase) (hInv.trans_le hDν)
    have hν : D⁻¹ ≤ w.physicalNu d.waveVector d.amplitude t :=
      (h.trans_eq (inv_inv _)).trans (d.first_coupling_lower t ht)
    exact raw_center_coupling_lower _ (d.transverse t ht).1 (d.transverse t ht).2.1 hν

end MovingWaveVector.PhysicalAmplification

private theorem leading_seed_weight_scale {freq : ℝ} (hf : 1 ≤ freq) :
    freq ^ (-1 / 2 : ℝ) = freq ^ (-5 / 4 : ℝ) * freq ^ (3 / 4 : ℝ) := by
  rw [← Real.rpow_add (zero_lt_one.trans_le hf)]
  norm_num

/-- The actual leading profile has the order-zero weighted size in (5.25),
including multiplication by a switch between zero and one. -/
theorem norm_switchedLeadingProfile_div_seedWeight_le {freq ell χ : ℝ}
    {a : Vec3 → Vec3} (hf : 1 ≤ freq) (hell : 0 < ell) (hχ : 0 ≤ χ) (hχ₁ : χ ≤ 1)
    (ha₀ : a 0 ≠ 0) (ha : ∀ x, ‖x‖ ≤ 2 * ell → ‖a x‖ ≤ 2 * ‖a 0‖)
    (x : Vec3) (s : ℝ) :
    ‖((χ * radialEnvelope ell x) * waveProfile (freq ^ (-1 / 2 : ℝ)) s) • a x‖ /
      (freq ^ (3 / 4 : ℝ) * ‖a 0‖) ≤ freq ^ (-5 / 4 : ℝ) := by
  let h := freq ^ (-1 / 2 : ℝ)
  have hγ : 0 < freq ^ (3 / 4 : ℝ) * ‖a 0‖ := by positivity
  have hwidth : 0 < h ∧ h ≤ 1 := (profileWidth_and_seedScale hf).1
  have hw := norm_waveProfile_le hwidth.1 hwidth.2 s
  have hcut₀ : 0 ≤ χ * radialEnvelope ell x :=
    mul_nonneg hχ (radialEnvelope_mem_Icc ell x).1
  have hcut₁ : χ * radialEnvelope ell x ≤ 1 := by
    nlinarith only [mul_le_mul hχ₁ (radialEnvelope_mem_Icc ell x).2
      (radialEnvelope_mem_Icc ell x).1 zero_le_one]
  apply (div_le_iff₀ hγ).2
  rw [← mul_assoc (freq ^ (-5 / 4 : ℝ)), ← leading_seed_weight_scale hf]
  change ‖((χ * radialEnvelope ell x) * waveProfile h s) • a x‖ ≤ h * ‖a 0‖
  by_cases hx : ‖x‖ ≤ 2 * ell
  · rw [norm_smul, norm_mul, Real.norm_of_nonneg hcut₀]
    calc
      _ ≤ (1 * (h / 2)) * (2 * ‖a 0‖) :=
        mul_le_mul (mul_le_mul hcut₁ hw (norm_nonneg _) zero_le_one) (ha x hx)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hg := radialEnvelope_eq_zero hell (le_of_not_ge hx)
    rw [hg, mul_zero, zero_mul, zero_smul, norm_zero]
    exact mul_nonneg hwidth.1.le (norm_nonneg _)

/-- The actual pressure associated to the leading profile has the other
order-zero weighted size in (5.25), including the factor of `freq`. -/
theorem freq_mul_norm_switchedLeadingPressure_div_seedWeight_le
    {freq ell χ D : ℝ} {a κ : Vec3 → Vec3} {M : Vec3 → Vec3 →L[ℝ] Vec3}
    (hf : 1 ≤ freq) (hell : 0 < ell) (hχ : 0 ≤ χ) (hχ₁ : χ ≤ 1)
    (hD : 1 ≤ D) (ha₀ : a 0 ≠ 0)
    (ha : ∀ x, ‖x‖ ≤ 2 * ell → ‖a x‖ ≤ 2 * ‖a 0‖)
    (hκ : ∀ x, ‖x‖ ≤ 2 * ell → freq ≤ D ^ 2 * ‖κ x‖)
    (hM : ∀ x, ‖x‖ ≤ 2 * ell → ‖M x‖ ≤ D)
    (x : Vec3) (s : ℝ) :
    freq * ‖oscillatoryPhasePressure (M x) (κ x) (fun _ => 0)
      (fun σ => ((χ * radialEnvelope ell x) * waveProfile (freq ^ (-1 / 2 : ℝ)) σ) • a x) s‖ /
      (freq ^ (3 / 4 : ℝ) * ‖a 0‖) ≤
      4 * D ^ 3 * freq ^ (-5 / 4 : ℝ) := by
  let h := freq ^ (-1 / 2 : ℝ)
  have hf₀ := zero_lt_one.trans_le hf
  have hγ : 0 < freq ^ (3 / 4 : ℝ) * ‖a 0‖ := by positivity
  have hwidth : 0 < h ∧ h ≤ 1 := (profileWidth_and_seedScale hf).1
  have hw : ‖wavePressurePrimitive h s‖ ≤ h := by
    unfold wavePressurePrimitive
    have hu := norm_phasePrimitive_le (contDiff_waveProfile hwidth.1 hwidth.2).continuous
      (periodic_waveProfile hwidth.1 hwidth.2) (phaseMean_waveProfile hwidth.1 hwidth.2)
      (fun σ _ => norm_waveProfile_le hwidth.1 hwidth.2 σ) s
    linarith only [hu]
  have hcut₀ : 0 ≤ χ * radialEnvelope ell x :=
    mul_nonneg hχ (radialEnvelope_mem_Icc ell x).1
  have hcut₁ : χ * radialEnvelope ell x ≤ 1 := by
    nlinarith only [mul_le_mul hχ₁ (radialEnvelope_mem_Icc ell x).2
      (radialEnvelope_mem_Icc ell x).1 zero_le_one]
  rw [oscillatoryPhasePressure_primary_eq]
  apply (div_le_iff₀ hγ).2
  have hscale : 4 * D ^ 3 * freq ^ (-5 / 4 : ℝ) *
      (freq ^ (3 / 4 : ℝ) * ‖a 0‖) = 4 * D ^ 3 * h * ‖a 0‖ := by
    rw [← mul_assoc _ (freq ^ (3 / 4 : ℝ)) ‖a 0‖, mul_assoc (4 * D ^ 3),
      ← leading_seed_weight_scale hf]
  rw [hscale]
  by_cases hx : ‖x‖ ≤ 2 * ell
  · have hkpos : 0 < ‖κ x‖ := by
      by_contra! hk
      have hk₀ := le_antisymm hk (norm_nonneg _)
      have hκx := hκ x hx
      rw [hk₀, mul_zero] at hκx
      exact (not_le_of_gt hf₀) hκx
    have hdot : ‖⟪κ x, M x (a x)⟫_ℝ‖ ≤ ‖κ x‖ * (D * ‖a x‖) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        (((M x).le_opNorm (a x)).trans (mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)))
        hkpos.le)
    have hc : ‖wavePressureCoefficient (χ * radialEnvelope ell x) (κ x) (a x) (M x)‖ ≤
        2 * (D * ‖a x‖) / ‖κ x‖ := by
      rw [wavePressureCoefficient, norm_div, norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
        Real.norm_of_nonneg hcut₀, Real.norm_of_nonneg (sq_nonneg _)]
      have hn : 2 * (χ * radialEnvelope ell x) * ‖⟪κ x, M x (a x)⟫_ℝ‖ ≤
          2 * 1 * (‖κ x‖ * (D * ‖a x‖)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcut₁ (by norm_num)) hdot
          (norm_nonneg _) (by positivity)
      calc
        _ ≤ 2 * 1 * (‖κ x‖ * (D * ‖a x‖)) / ‖κ x‖ ^ 2 :=
          div_le_div_of_nonneg_right hn (sq_nonneg _)
        _ = _ := by field_simp [hkpos.ne']
    have hc' : freq * ‖wavePressureCoefficient (χ * radialEnvelope ell x) (κ x) (a x) (M x)‖ ≤
        4 * D ^ 3 * ‖a 0‖ := by
      calc
        _ ≤ freq * (2 * (D * ‖a x‖) / ‖κ x‖) := mul_le_mul_of_nonneg_left hc hf₀.le
        _ = (freq / ‖κ x‖) * (2 * (D * ‖a x‖)) := by ring
        _ ≤ D ^ 2 * (2 * (D * (2 * ‖a 0‖))) :=
          mul_le_mul ((div_le_iff₀ hkpos).mpr (hκ x hx)) (by gcongr; exact ha x hx)
            (by positivity) (by positivity)
        _ = _ := by ring
    rw [norm_mul, norm_neg, ← mul_assoc]
    calc
      _ ≤ (4 * D ^ 3 * ‖a 0‖) * h :=
        mul_le_mul hc' hw (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hg := radialEnvelope_eq_zero hell (le_of_not_ge hx)
    simp only [hg, mul_zero, wavePressureCoefficient, zero_mul, zero_div, neg_zero, norm_zero]
    positivity


private theorem exists_scaled_deriv_waveProfile_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h, 0 < h → h ≤ 1 → ∀ s,
      h ^ j * ‖iteratedDeriv j (waveProfile h) s‖ ≤ C * h := by
  cases j with
  | zero =>
      refine ⟨1, by norm_num, fun h hh h₁ s => ?_⟩
      simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
        (norm_waveProfile_le hh h₁ s).trans (show h / 2 ≤ h by linarith)
  | succ j =>
      cases j with
      | zero =>
          refine ⟨1, zero_lt_one, fun h hh h₁ s => ?_⟩
          have ho := deriv_waveProfile_bounds hh h₁ s
          have hnorm : ‖deriv (waveProfile h) s‖ ≤ 1 := by
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [ho.1], ho.2⟩
          simpa only [Nat.zero_add, pow_one, iteratedDeriv_one, mul_one, one_mul]
            using mul_le_mul_of_nonneg_left hnorm hh.le
      | succ j =>
          obtain ⟨C, hC, h⟩ := exists_iteratedDeriv_waveProfile_bound (j + 1 + 1) (by omega)
          refine ⟨C, hC, fun h₀ hh h₁ s => ?_⟩
          calc
            _ ≤ h₀ ^ (j + 1 + 1) * (C * h₀ ^ (1 - ((j + 1 + 1 : ℕ) : ℤ))) :=
              mul_le_mul_of_nonneg_left (h h₀ hh h₁ s) (by positivity)
            _ = _ := by
              rw [mul_left_comm, ← zpow_natCast h₀ (j + 1 + 1), ← zpow_add₀ hh.ne']
              congr 1
              have he : (((j + 1 + 1 : ℕ) : ℤ) + (1 - ((j + 1 + 1 : ℕ) : ℤ))) = 1 := by omega
              rw [he, zpow_one]

private theorem phaseJetBound_scaledPhaseOnly {f : ℝ → ℝ} {n : ℕ} {h C : ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : 0 < h)
    (hderiv : ∀ j ≤ n, ∀ s, h ^ j * ‖iteratedDeriv j f s‖ ≤ C) :
    PhaseJetBound n C (fun p : Vec3 × ℝ => f (h * p.2)) := by
  let L : (Vec3 × ℝ) →L[ℝ] ℝ := h • ContinuousLinearMap.snd ℝ Vec3 ℝ
  have hL : ‖L‖ ≤ h := by
    rw [show L = h • ContinuousLinearMap.snd ℝ Vec3 ℝ from rfl, norm_smul,
      Real.norm_of_nonneg hh.le]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ Vec3 ℝ) hh.le)
  intro j hj p
  change ‖iteratedFDeriv ℝ j (f ∘ L) p‖ ≤ C
  rw [L.iteratedFDeriv_comp_right hf p (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L p)‖ * ‖L‖ ^ j := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ j f (L p))
          (fun _ => L)
    _ ≤ ‖iteratedFDeriv ℝ j f (L p)‖ * h ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL j) (norm_nonneg _)
    _ ≤ C := by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, mul_comm]; exact hderiv j hj _

/-- Scaling the phase variable by the profile width gives uniform finite
derivative bounds for the wave and its pressure primitive. -/
theorem exists_scaled_wavePhaseJetBounds (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h, 0 < h → h ≤ 1 →
      PhaseJetBound n (C * h) (fun p : Vec3 × ℝ => waveProfile h (h * p.2)) ∧
      PhaseJetBound n (C * h) (fun p : Vec3 × ℝ => wavePressurePrimitive h (h * p.2)) := by
  classical
  choose B hB hBD using exists_scaled_deriv_waveProfile_bound
  let C := 1 + ∑ j ∈ Finset.range (n + 1), B j
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => (hB j).le)
  have hLe (j : ℕ) (hj : j ≤ n) : B j ≤ C := by
    have hmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hsum := Finset.single_le_sum (f := B) (fun k _ => (hB k).le) hmem
    have htotal : (∑ k ∈ Finset.range (n + 1), B k) ≤ C := by
      dsimp only [C]
      linarith
    exact hsum.trans htotal
  refine ⟨C, hC, fun h hh h₁ => ?_⟩
  have hw (j : ℕ) (hj : j ≤ n) (s : ℝ) :
      h ^ j * ‖iteratedDeriv j (waveProfile h) s‖ ≤ C * h :=
    (hBD j h hh h₁ s).trans (mul_le_mul_of_nonneg_right (hLe j hj) hh.le)
  refine ⟨phaseJetBound_scaledPhaseOnly (contDiff_waveProfile hh h₁) hh hw,
    phaseJetBound_scaledPhaseOnly (contDiff_wavePressurePrimitive hh h₁) hh ?_⟩
  intro j hj s
  cases j with
  | zero =>
      rw [pow_zero, one_mul, iteratedDeriv_zero]
      unfold wavePressurePrimitive
      have hp := norm_phasePrimitive_le (contDiff_waveProfile hh h₁).continuous
        (periodic_waveProfile hh h₁) (phaseMean_waveProfile hh h₁)
        (fun σ _ => norm_waveProfile_le hh h₁ σ) s
      exact (show ‖phasePrimitive (waveProfile h) s‖ ≤ h by linarith only [hp]).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hh.le)
  | succ j =>
      have heq : deriv (wavePressurePrimitive h) = waveProfile h :=
        funext fun x => (hasDerivAt_wavePressurePrimitive hh h₁ x).deriv
      rw [iteratedDeriv_succ', heq, pow_succ, mul_comm (h ^ j), mul_assoc]
      exact (mul_le_mul_of_nonneg_left (hw j (by omega) s) hh.le).trans
        (mul_le_of_le_one_left (by positivity) h₁)


private theorem phaseJetBound_smul_localized {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} {g : E → F} {n : ℕ} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hfB : PhaseJetBound n A f) (hgB : PhaseJetBound n B g) :
    PhaseJetBound n ((2 : ℝ) ^ n * A * B) (fun x => f x • g x) := by
  intro j hj x
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      norm_iteratedFDeriv_smul_le hf hg x (by simp)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfB i (hij.trans hj) x) (Nat.cast_nonneg _))
        (hgB (j - i) ((Nat.sub_le j i).trans hj) x) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ j * A * B := by
      have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ)^j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB

/-- The finite-order leading profile and pressure bounds follow from the
corresponding slow-factor bounds. The pressure slow factor includes the
frequency normalization in (5.25). -/
theorem exists_switchedLeadingProfile_scaledJetBounds (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {freq ell χ γ U Q : ℝ} {a κ : Vec3 → Vec3}
      {M : Vec3 → (Vec3 →L[ℝ] Vec3)},
      1 ≤ freq → 0 ≤ γ → 0 ≤ U → 0 ≤ Q →
      let h := freq ^ (-1 / 2 : ℝ)
      let F (p : Vec3 × ℝ) := (χ * radialEnvelope ell (ell • p.1)) • a (ell • p.1)
      let P (p : Vec3 × ℝ) := freq * -wavePressureCoefficient
        (χ * radialEnvelope ell (ell • p.1)) (κ (ell • p.1)) (a (ell • p.1)) (M (ell • p.1))
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ P →
      PhaseJetBound n (U * γ * freq ^ (-3 / 4 : ℝ)) F →
      PhaseJetBound n (Q * γ * freq ^ (-3 / 4 : ℝ)) P →
      PhaseJetBound n (γ * (C * U * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile ell h
          (fun x s => ((χ * radialEnvelope ell x) * waveProfile h s) • a x)) ∧
      PhaseJetBound n (γ * (C * Q * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile ell h (fun x s =>
          freq * oscillatoryPhasePressure (M x) (κ x) (fun _ => 0)
            (fun σ => ((χ * radialEnvelope ell x) * waveProfile h σ) • a x) s)) := by
  obtain ⟨C, hC, hBase⟩ := exists_scaled_wavePhaseJetBounds n
  let B := (2 : ℝ) ^ n * C
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)]
  refine ⟨B, hB, ?_⟩
  intro freq ell χ γ U Q a κ M hf hγ hU hQ h F P hF hP hFU hPQ
  have hwidth : (0 < h ∧ h ≤ 1) ∧ freq ^ (-3 / 4 : ℝ) * h = freq ^ (-5 / 4 : ℝ) :=
    profileWidth_and_seedScale hf
  obtain ⟨hWave, hPrim⟩ := hBase h hwidth.1.1 hwidth.1.2
  let L : (Vec3 × ℝ) →L[ℝ] ℝ := h • ContinuousLinearMap.snd ℝ Vec3 ℝ
  have hw : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => waveProfile h (h * p.2)) :=
    (contDiff_waveProfile hwidth.1.1 hwidth.1.2).comp L.contDiff
  have hp : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => wavePressurePrimitive h (h * p.2)) :=
    (contDiff_wavePressurePrimitive hwidth.1.1 hwidth.1.2).comp L.contDiff
  have hV' := phaseJetBound_smul_localized hw hF (by positivity) (by positivity) hWave hFU
  have hP' := phaseJetBound_smul_localized hp hP (by positivity) (by positivity) hPrim hPQ
  have hvEq :
      scaledPhaseProfile ell h (fun x s => ((χ * radialEnvelope ell x) * waveProfile h s) • a x) =
        fun p => waveProfile h (h * p.2) • F p := by
    funext p
    simp only [scaledPhaseProfile, Function.comp_def, labelPhaseScale_apply, Function.uncurry,
      F, smul_smul]
    rw [mul_comm (waveProfile h (h * p.2))]
  have hpEq :
      scaledPhaseProfile ell h (fun x s => freq * oscillatoryPhasePressure (M x) (κ x)
        (fun _ => 0) (fun σ => ((χ * radialEnvelope ell x) * waveProfile h σ) • a x) s) =
      fun p => wavePressurePrimitive h (h * p.2) • P p := by
    funext p
    simp only [scaledPhaseProfile, Function.comp_def, labelPhaseScale_apply, Function.uncurry,
      P, oscillatoryPhasePressure_primary_eq, smul_eq_mul]
    ring
  have hs (A : ℝ) : (2 : ℝ) ^ n * (C * h) * (A * γ * freq ^ (-3 / 4 : ℝ)) =
      γ * (B * A * freq ^ (-5 / 4 : ℝ)) := by
    rw [← hwidth.2]
    dsimp only [B]
    ring
  exact ⟨by rw [hvEq, ← hs]; exact hV', by rw [hpEq, ← hs]; exact hP'⟩

/-- The odd parent fixes the zero label. A central covector prescribed at
activation is the inverse-transpose image of its time-zero label covector
throughout the physical slab. -/
theorem IsLabelFlowOn.center_coframe_covector_eq
    {U : Velocity} {X : ℝ → Velocity} {T t₀ : ℝ} {κ : ℝ → Vec3}
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hT : 0 < T)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hodd : ∀ t ∈ Icc 0 T, Function.Odd (U t))
    (h₀ : t₀ ∈ Icc 0 T)
    (hκ : ∀ t ∈ Icc t₀ T, HasDerivWithinAt κ
      (-((fderiv ℝ (U t) (0 : Vec3)).adjoint (κ t))) (Icc t₀ T) t) :
    let k := (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (κ t₀)
    (κ t₀ ≠ 0 → k ≠ 0) ∧
      ∀ t ∈ Icc t₀ T, (fderiv ℝ (X t 0) (0 : Vec3)).adjoint k = κ t := by
  let k := (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (κ t₀)
  let b := labelWaveVector X 0 (0 : Vec3) k
  let A (t : ℝ) := -(fderiv ℝ (U t) (0 : Vec3)).adjoint
  have h0T : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hsub : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left h₀.1
  have ht₀ : t₀ ∈ Icc t₀ T := left_mem_Icc.mpr h₀.2
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by norm_num)) hper
  have hfix (t : ℝ) (ht : t ∈ Icc 0 T) : X 0 t (0 : Vec3) = 0 := by
    have heq := hX.odd hL hodd h0T ht (0 : Vec3)
    rw [neg_zero] at heq
    ext i
    have hi := congrArg (fun y : Vec3 => y i) heq
    simp only [PiLp.neg_apply] at hi
    simpa only [PiLp.zero_apply] using (show (X 0 t 0) i = 0 by linarith)
  have hb (t : ℝ) (ht : t ∈ Icc t₀ T) :
      HasDerivWithinAt b (A t (b t)) (Icc t₀ T) t := by
    simpa only [b, A, neg_apply, hfix t (hsub ht)] using
      (hX.hasDerivWithinAt_labelWaveVector hT hU hper h0T (hsub ht) 0 k).mono hsub
  have hgrad : ContDiffOn ℝ 1 (fun p : ℝ × Vec3 => fderiv ℝ (U p.1) p.2)
      (Icc 0 T ×ˢ univ) :=
    contDiffOn_spatialDerivative_of_joint_contDiff (n := 1) (uniqueDiffOn_Icc hT)
      (by
        convert hU using 1
        norm_num)
  have hM : ContinuousOn (fun t => fderiv ℝ (U t) (0 : Vec3)) (Icc 0 T) :=
    hgrad.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht, mem_univ _⟩)
  have hAc : ContinuousOn A (Icc t₀ T) :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn (hM.mono hsub)).neg
  have hI := (hX.labelDerivative_inverse hT hU hper h0T h₀ (0 : Vec3)).2
  rw [hfix t₀ h₀] at hI
  have hAdj := congrArg (ContinuousLinearMap.adjoint (𝕜 := ℝ)) hI
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hAdj
  have hStart : b t₀ = κ t₀ := by
    simpa only [b, labelWaveVector, hfix t₀ h₀, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, k] using DFunLike.congr_fun hAdj (κ t₀)
  have hEqual := linearODE_unique_of_mem ordConnected_Icc ht₀ hAc hb
    (fun t ht => by simpa only [A, neg_apply] using hκ t ht) hStart
  have htransport (t : ℝ) (ht : t ∈ Icc t₀ T) :
      (fderiv ℝ (X t 0) (0 : Vec3)).adjoint k = κ t := by
    simpa only [b, labelWaveVector, hfix t (hsub ht)] using hEqual ht
  refine ⟨fun hκ₀ hk => hκ₀ ?_, htransport⟩
  change k = 0 at hk
  rw [← htransport t₀ ht₀, hk, map_zero]

private theorem norm_label_difference_le_of_first_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Vec3 → V} {C : ℝ}
    (hf : Differentiable ℝ f) (hC : ∀ a, ‖iteratedFDeriv ℝ 1 f a‖ ≤ C) (a b : Vec3) :
    ‖f a - f b‖ ≤ C * ‖a - b‖ :=
  (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hf x) (fun x _ => by simpa only [norm_iteratedFDeriv_one] using hC x)
    (mem_univ b) (mem_univ a)

/-- The actual first parent coframe jets supply the label Lipschitz estimates
for the flow Jacobians, material gradient and transverse projection. The
transported wave-vector comparison is relative to the reference label. -/
theorem exists_parent_coefficient_label_lipschitz (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
        ∀ (k : Vec3) {Λ t₀ : ℝ}, 0 < Λ → t₀ ∈ Icc 0 T →
          ‖labelWaveVector X 0 0 k t₀‖ = Λ → ∀ t ∈ Icc 0 T, ∀ a b : Vec3,
          let F := fderiv ℝ (X 0 t)
          let G (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
          let M (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
          let κ (x : Vec3) := labelWaveVector X 0 x k t
          ‖F a - F b‖ ≤ C * D ^ 6 * ‖a - b‖ ∧
          ‖G a - G b‖ ≤ C * D ^ 8 * ‖a - b‖ ∧
          ‖M a - M b‖ ≤ C * D ^ 7 * ‖a - b‖ ∧
          ‖κ a - κ b‖ ≤ C * D ^ 11 * ‖a - b‖ * ‖κ b‖ ∧
          ‖oscillatoryTransverseProjection (κ a) - oscillatoryTransverseProjection (κ b)‖ ≤
            C * D ^ 24 * ‖a - b‖ := by
  obtain ⟨C, hC, hJets⟩ := exists_parent_coefficientJetBounds R hR
  refine ⟨C 1, hC 1, ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hG hUjet k Λ t₀ hΛ ht₀ hcenter t ht a b
  dsimp only
  let F := fderiv ℝ (X 0 t)
  let G (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
  let M (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
  let κ (x : Vec3) := labelWaveVector X 0 x k t
  let κN (x : Vec3) := Λ⁻¹ • κ x
  let P (x : Vec3) := (‖κ x‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (κ x) (κ x)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have hFlow : ContDiff ℝ 2 (X 0 t) := (hX.labelJets_evolve 2 hT hU hper).1 t ht
  have hFd : ContDiff ℝ 1 F := hFlow.fderiv_right (by norm_num)
  have hGd : ContDiff ℝ 1 G :=
    hX.contDiff_inverseLabelDerivative hT hU₂ hper h₀ ht (n := 1) hFlow
  have hU' : ContDiff ℝ ∞ (U t) :=
    contDiffOn_univ.mp (hU.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hGrad : ContDiff ℝ 1 (fderiv ℝ (U t)) :=
    ((contDiff_infty_iff_fderiv.mp hU').2).of_le (by simp)
  have hMd : ContDiff ℝ 1 M := hGrad.comp (hFlow.of_le (by norm_num))
  let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  have hκd : ContDiff ℝ 1 κ := (J.toContinuousLinearEquiv.contDiff.comp hGd).clm_apply contDiff_const
  have hκNd : ContDiff ℝ 1 κN := by
    change ContDiff ℝ 1 (fun x => Λ⁻¹ • κ x)
    exact (contDiff_const (c := Λ⁻¹)).smul hκd
  have hLower (x : Vec3) : (D ^ 2)⁻¹ ≤ ‖κN x‖ :=
    (hX.norm_normalizedLabelWaveVector_bounds hT hU₂ hper ht₀ ht x k hD hΛ hcenter
      (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t ht x) (hG t ht x)).2.1
  have hκnz (x : Vec3) : κ x ≠ 0 := by
    intro hzero
    have h := hLower x
    simp only [κN, hzero, smul_zero, norm_zero] at h
    exact (not_le_of_gt (show 0 < (D ^ 2)⁻¹ by positivity)) h
  have hQ : ContDiff ℝ 1 (fun x => ‖κ x‖ ^ 2) := by
    simp_rw [← real_inner_self_eq_norm_sq]
    exact ((innerSL ℝ (E := Vec3)).contDiff.comp hκd).clm_apply hκd
  let A : Vec3 →L[ℝ] (Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3)) := InnerProductSpace.rankOne ℝ
  have hPRank : ContDiff ℝ 1 (fun x => InnerProductSpace.rankOne ℝ (κ x) (κ x)) := by
    change ContDiff ℝ 1 (fun x => A (κ x) (κ x))
    exact (A.contDiff.comp hκd).clm_apply hκd
  have hPd : ContDiff ℝ 1 P :=
    (hQ.inv fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκnz x))).smul hPRank
  have hJet (x : Vec3) := hJets hT hT₁ hD hX hU hper hF hG hUjet k hΛ ht₀ hcenter 1 t ht x
  have hFdiff := norm_label_difference_le_of_first_jet (hFd.differentiable (by norm_num))
    (fun x => (hJet x).1) a b
  have hGdiff := norm_label_difference_le_of_first_jet (hGd.differentiable (by norm_num))
    (fun x => (hJet x).2.1) a b
  have hMdiff := norm_label_difference_le_of_first_jet (hMd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.2.1) a b
  have hκNdiff := norm_label_difference_le_of_first_jet (hκNd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.2.2.1) a b
  have hPdiff := norm_label_difference_le_of_first_jet (hPd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.2.2.2.2) a b
  have hNorm (v : Vec3) : ‖Λ⁻¹ • v‖ = ‖v‖ / Λ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ), div_eq_mul_inv, mul_comm]
  have hκAbs : ‖κ a - κ b‖ ≤ C 1 * D ^ 9 * ‖a - b‖ * Λ := by
    change ‖Λ⁻¹ • κ a - Λ⁻¹ • κ b‖ ≤ C 1 * D ^ 9 * ‖a - b‖ at hκNdiff
    rw [← smul_sub, hNorm] at hκNdiff
    exact (div_le_iff₀ hΛ).mp hκNdiff
  have hΛbound : Λ ≤ D ^ 2 * ‖κ b‖ := by
    have hx := hLower b
    change (D ^ 2)⁻¹ ≤ ‖Λ⁻¹ • κ b‖ at hx
    rw [hNorm, ← one_div (D ^ 2)] at hx
    have hl := (div_le_div_iff₀ (by positivity : 0 < D ^ 2) hΛ).mp hx
    simpa only [one_mul, mul_one, mul_comm] using hl
  have hκdiff : ‖κ a - κ b‖ ≤ C 1 * D ^ 11 * ‖a - b‖ * ‖κ b‖ := by
    calc
      _ ≤ C 1 * D ^ 9 * ‖a - b‖ * Λ := hκAbs
      _ ≤ C 1 * D ^ 9 * ‖a - b‖ * (D ^ 2 * ‖κ b‖) :=
        mul_le_mul_of_nonneg_left hΛbound
          (mul_nonneg (mul_nonneg (hC 1) (by positivity)) (norm_nonneg _))
      _ = _ := by ring
  have hQdiff :
      ‖oscillatoryTransverseProjection (κ a) - oscillatoryTransverseProjection (κ b)‖ =
        ‖P a - P b‖ := by
    change ‖(.id ℝ Vec3 - P a) - (.id ℝ Vec3 - P b)‖ = _
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
  exact ⟨hFdiff, hGdiff, hMdiff, hκdiff, hQdiff.trans_le hPdiff⟩

/-- An envelope radius chosen as a sufficiently negative power of the parent
parameter absorbs a fixed polynomial label Lipschitz bound. -/
theorem exists_envelopeExponent_for_label_error (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (p q : ℕ) :
    ∃ A : ℕ, 3 ≤ A ∧ ∀ {D ell : ℝ}, 2 ≤ D → ell ≤ (D ^ A)⁻¹ →
      C * D ^ p * (2 * ell) ≤ c * (D ^ q)⁻¹ := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * C / c) (by norm_num : (1 : ℝ) < 2)
  refine ⟨p + q + (n + 3), by omega, ?_⟩
  intro D ell hD hell
  have hDpos : 0 < D := by linarith
  have hpow : 2 * C / c ≤ D ^ (n + 3) :=
    hn.le.trans ((pow_le_pow_left₀ (by norm_num) hD n).trans
      (pow_le_pow_right₀ (by linarith) (by omega)))
  have hratio : 2 * C / D ^ (n + 3) ≤ c := by
    apply (div_le_iff₀ (pow_pos hDpos _)).2
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hpow
  calc
    _ ≤ C * D ^ p * (2 * (D ^ (p + q + (n + 3)))⁻¹) := by gcongr
    _ = (2 * C / D ^ (n + 3)) * (D ^ q)⁻¹ := by
      rw [pow_add D (p + q) (n + 3), pow_add D p q]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)

end TorusEuler

namespace TorusEuler.LocalizedAmplitude

/-- The positive center weight has a continuous derivative on the closed slab. -/
theorem norm_hasContinuous_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f df : ℝ → E} {I : Set ℝ}
    (hd : ∀ t ∈ I, HasDerivWithinAt f (df t) I t)
    (hdf : ContinuousOn df I) (hf₀ : ∀ t ∈ I, f t ≠ 0) :
    ∃ dg : ℝ → ℝ, ContinuousOn dg I ∧ ∀ t ∈ I,
      HasDerivWithinAt (fun u => ‖f u‖) (dg t) I t := by
  let g (t : ℝ) := ⟪f t, df t⟫_ℝ / ‖f t‖
  have hc := HasDerivWithinAt.continuousOn hd
  refine ⟨g, (hc.inner hdf).div hc.norm (fun t ht => norm_ne_zero_iff.mpr (hf₀ t ht)),
    fun t ht => ?_⟩
  have hn : 0 < ‖f t‖ := norm_pos_iff.mpr (hf₀ t ht)
  have h := (hd t ht).norm_sq.sqrt (show 0 < ‖f t‖ ^ 2 by positivity).ne'
  have hEq : (fun u => Real.sqrt (‖f u‖ ^ 2)) = fun u => ‖f u‖ :=
    funext fun u => Real.sqrt_sq (norm_nonneg _)
  rw [hEq, Real.sqrt_sq (norm_nonneg _)] at h
  refine h.congr_deriv ?_
  dsimp [g]
  ring_nf

/-- Transfer the coordinate error to the physical seed. The last term is
the change of the moving transverse frame itself. -/
theorem physical_error_le_of_coordinates
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {J J₀ : E →L[ℝ] V} {x y : E} {D L B d g : ℝ}
    (hJ : ‖J‖ ≤ D) (hΔJ : ‖J - J₀‖ ≤ L * d)
    (hy : ‖y‖ ≤ D * g) (hx : ‖x - y‖ ≤ B * d * g) :
    ‖J x - J₀ y‖ ≤ (D * B + L * D) * d * g := by
  have hD := (norm_nonneg _).trans hJ
  have hL := (norm_nonneg _).trans hΔJ
  have heq : J x - J₀ y = J (x - y) + (J - J₀) y := by
    rw [map_sub, sub_apply]
    abel
  rw [heq]
  calc
    _ ≤ ‖J (x - y)‖ + ‖(J - J₀) y‖ := norm_add_le _ _
    _ ≤ ‖J‖ * ‖x - y‖ + ‖J - J₀‖ * ‖y‖ :=
      add_le_add (J.le_opNorm _) ((J - J₀).le_opNorm _)
    _ ≤ D * (B * d * g) + (L * d) * (D * g) :=
      add_le_add (mul_le_mul hJ hx (norm_nonneg _) hD)
        (mul_le_mul hΔJ hy (norm_nonneg _) hL)
    _ = _ := by ring

/-- The transported wave vector changes at most proportionally to the inverse
coframe change and to the length of its initial covector. -/
theorem norm_relative_covector_error_le
    {G G₀ : Vec3 →L[ℝ] Vec3} {k : Vec3} {D L d : ℝ}
    (hΔ : ‖G - G₀‖ ≤ L * d) (hk : ‖k‖ ≤ D * ‖G₀.adjoint k‖) :
    ‖G.adjoint k - G₀.adjoint k‖ ≤ (L * D) * d * ‖G₀.adjoint k‖ := by
  have hL := (norm_nonneg _).trans hΔ
  have heq : G.adjoint k - G₀.adjoint k = (G - G₀).adjoint k := by
    rw [map_sub, sub_apply]
  rw [heq]
  calc
    _ ≤ ‖(G - G₀).adjoint‖ * ‖k‖ := (G - G₀).adjoint.le_opNorm _
    _ ≤ (L * d) * (D * ‖G₀.adjoint k‖) := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul hΔ hk (norm_nonneg _) hL
    _ = _ := by ring


/-- Forward frame on the fixed transverse plane of the launch covector. -/
noncomputable def coframeLift (k : Vec3) (F : Vec3 →L[ℝ] Vec3) :
    transversePlane k →L[ℝ] Vec3 :=
  F.comp (transversePlane k).subtypeL

/-- Backward frame. Project onto the physical transverse plane first, then
apply the inverse deformation. -/
noncomputable def coframePullback (k : Vec3) (G : Vec3 →L[ℝ] Vec3) :
    Vec3 →L[ℝ] transversePlane k :=
  (transversePlane k).orthogonalProjectionOnto.comp
    (G.comp (oscillatoryTransverseProjection (G.adjoint k)))

private theorem inverse_coframe_maps_projected (k : Vec3) (G : Vec3 →L[ℝ] Vec3) (z : Vec3) :
    G (oscillatoryTransverseProjection (G.adjoint k) z) ∈ transversePlane k := by
  change ⟪k, G (oscillatoryTransverseProjection (G.adjoint k) z)⟫_ℝ = 0
  rw [← ContinuousLinearMap.adjoint_inner_left]
  by_cases hk : G.adjoint k = 0
  · simp [hk]
  · exact inner_oscillatoryTransverseProjection _ _ hk

private theorem coframePullback_coe (k : Vec3) (G : Vec3 →L[ℝ] Vec3) (z : Vec3) :
    (coframePullback k G z : Vec3) = G (oscillatoryTransverseProjection (G.adjoint k) z) := by
  exact congrArg Subtype.val
    ((transversePlane k).orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨_, inverse_coframe_maps_projected k G z⟩)

/-- These are the two identities for the frame and its projected inverse in
(5.20). The fixed plane carries its inherited Euclidean norm. -/
theorem coframe_identities (k : Vec3) {F G : Vec3 →L[ℝ] Vec3}
    (hGF : G.comp F = .id ℝ Vec3) (hFG : F.comp G = .id ℝ Vec3) :
    (coframePullback k G).comp (coframeLift k F) = .id ℝ (transversePlane k) ∧
      (coframeLift k F).comp (coframePullback k G) =
        oscillatoryTransverseProjection (G.adjoint k) := by
  have hleft (z : Vec3) : G (F z) = z :=
    congrArg (fun L : Vec3 →L[ℝ] Vec3 => L z) hGF
  have hright (z : Vec3) : F (G z) = z :=
    congrArg (fun L : Vec3 →L[ℝ] Vec3 => L z) hFG
  constructor
  · apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change (coframePullback k G (F z) : Vec3) = z
    have hp : ⟪G.adjoint k, F z⟫_ℝ = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_left, hleft]
      exact z.property
    rw [coframePullback_coe, oscillatoryTransverseProjection_apply, hp, zero_div, zero_smul,
      sub_zero, hleft]
  · apply ContinuousLinearMap.ext
    intro z
    change F (coframePullback k G z : Vec3) = _
    rw [coframePullback_coe, hright]

theorem norm_coframeLift_le (k : Vec3) (F : Vec3 →L[ℝ] Vec3) :
    ‖coframeLift k F‖ ≤ ‖F‖ :=
  (F.opNorm_comp_le _).trans
    ((mul_le_mul_of_nonneg_left (transversePlane k).norm_subtypeL_le (norm_nonneg F)).trans_eq
      (mul_one _))

theorem norm_coframePullback_le (k : Vec3) (G : Vec3 →L[ℝ] Vec3) :
    ‖coframePullback k G‖ ≤ ‖G‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro z
  change ‖(coframePullback k G z : Vec3)‖ ≤ _
  rw [coframePullback_coe]
  refine (G.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg G))
  by_cases hk : G.adjoint k = 0
  · simp [hk, oscillatoryTransverseProjection_apply]
  · exact norm_oscillatoryTransverseProjection_le _ _ hk

theorem coframeLift_hasDerivWithinAt (k : Vec3) {F M : ℝ → Vec3 →L[ℝ] Vec3}
    {I : Set ℝ} {t : ℝ} (hF : HasDerivWithinAt F ((M t).comp (F t)) I t) :
    HasDerivWithinAt (fun u => coframeLift k (F u))
      ((M t).comp (coframeLift k (F t))) I t := by
  let L := (compL ℝ (transversePlane k) Vec3 Vec3).flip (transversePlane k).subtypeL
  exact L.hasFDerivAt.comp_hasDerivWithinAt t hF

theorem coframePullback_continuousOn (k : Vec3) {G : ℝ → Vec3 →L[ℝ] Vec3}
    {I : Set ℝ} (hG : ContinuousOn G I) (hk : ∀ t ∈ I, (G t).adjoint k ≠ 0) :
    ContinuousOn (fun t => coframePullback k (G t)) I := by
  have hAdj := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).continuous
  have hκ : ContinuousOn (fun t => (G t).adjoint k) I :=
    (hAdj.comp_continuousOn hG).clm_apply continuousOn_const
  exact continuousOn_const.clm_comp
    (hG.clm_comp (continuousOn_oscillatoryTransverseProjection hκ hk))

theorem norm_coframeLift_sub_le (k : Vec3) (F F₀ : Vec3 →L[ℝ] Vec3) :
    ‖coframeLift k F - coframeLift k F₀‖ ≤ ‖F - F₀‖ := by
  convert norm_coframeLift_le k (F - F₀) using 1
  rw [coframeLift, coframeLift, coframeLift, ContinuousLinearMap.sub_comp]

theorem norm_coframePullback_sub_le (k : Vec3) (G G₀ : Vec3 →L[ℝ] Vec3) :
    ‖coframePullback k G - coframePullback k G₀‖ ≤
      ‖G - G₀‖ + ‖G₀‖ *
        ‖oscillatoryTransverseProjection (G.adjoint k) -
          oscillatoryTransverseProjection (G₀.adjoint k)‖ := by
  apply opNorm_le_bound _ (by positivity)
  intro z
  let P := oscillatoryTransverseProjection (G.adjoint k)
  let P₀ := oscillatoryTransverseProjection (G₀.adjoint k)
  have heq : G (P z) - G₀ (P₀ z) = (G - G₀) (P z) + G₀ ((P - P₀) z) := by
    rw [sub_apply, sub_apply, map_sub]
    abel
  have hp : ‖P z‖ ≤ ‖z‖ := by
    by_cases hk : G.adjoint k = 0
    · simp [P, hk, oscillatoryTransverseProjection_apply]
    · exact norm_oscillatoryTransverseProjection_le _ _ hk
  change ‖(coframePullback k G z : Vec3) - (coframePullback k G₀ z : Vec3)‖ ≤ _
  rw [coframePullback_coe, coframePullback_coe]
  change ‖G (P z) - G₀ (P₀ z)‖ ≤ (‖G - G₀‖ + ‖G₀‖ * ‖P - P₀‖) * ‖z‖
  rw [heq, add_mul, mul_assoc]
  exact (norm_add_le _ _).trans (add_le_add
    (((G - G₀).le_opNorm _).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _)))
    ((G₀.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((P - P₀).le_opNorm _)
      (norm_nonneg _))))


private theorem norm_comp_sub_comp_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A A₀ : F →L[ℝ] G) (B B₀ : E →L[ℝ] F) :
    ‖A.comp B - A₀.comp B₀‖ ≤ ‖A - A₀‖ * ‖B‖ + ‖A₀‖ * ‖B - B₀‖ := by
  have heq : A.comp B - A₀.comp B₀ = (A - A₀).comp B + A₀.comp (B - B₀) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

/-- The fixed-coordinate generator varies at most by the sum of the frame,
matrix, and inverse-frame errors, multiplied by the two other norm bounds. -/
theorem norm_fixedTransverseGenerator_sub_le
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {M M₀ : Vec3 →L[ℝ] Vec3} {J J₀ : S →L[ℝ] Vec3} {R R₀ : Vec3 →L[ℝ] S}
    {D : ℝ} (hD : 0 ≤ D)
    (hM : ‖M‖ ≤ D) (hM₀ : ‖M₀‖ ≤ D) (hJ : ‖J‖ ≤ D) (hR₀ : ‖R₀‖ ≤ D) :
    ‖fixedTransverseGenerator M J R - fixedTransverseGenerator M₀ J₀ R₀‖ ≤
      2 * D ^ 2 * (‖J - J₀‖ + ‖R - R₀‖ + ‖M - M₀‖) := by
  have hMJ : ‖M.comp J‖ ≤ D * D :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hM hJ (norm_nonneg _) hD)
  have hΔMJ : ‖M.comp J - M₀.comp J₀‖ ≤ ‖M - M₀‖ * D + D * ‖J - J₀‖ :=
    (norm_comp_sub_comp_le M M₀ J J₀).trans (add_le_add
      (mul_le_mul_of_nonneg_left hJ (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hM₀ (norm_nonneg _)))
  have h := (norm_comp_sub_comp_le R R₀ (M.comp J) (M₀.comp J₀)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hMJ (norm_nonneg _))
      (mul_le_mul hR₀ hΔMJ (norm_nonneg _) hD))
  rw [fixedTransverseGenerator, fixedTransverseGenerator, ← smul_sub, norm_smul]
  rw [show ‖(-2 : ℝ)‖ = 2 by norm_num]
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans_eq (by ring)

/-- Label Lipschitz bound for the fixed-coordinate generator. -/
def generatorLabelSlope (D LF LG LM LP : ℝ) : ℝ :=
  2 * D ^ 2 * (LF + (LG + D * LP) + LM)

/-- The physical label error includes both Duhamel terms and the frame change. -/
noncomputable def amplitudeLabelSlope (D LF LG LM LP : ℝ) : ℝ :=
  D * (D ^ 3 * (LG + D * LP) + Real.exp 1 * (D ^ 3) ^ 2 * D *
    generatorLabelSlope D LF LG LM LP) + LF * D

/-- The common sensitivity of the amplitude, covector and material gradient. -/
noncomputable def nearLabelSlope (D LF LG LM LP : ℝ) : ℝ :=
  max (amplitudeLabelSlope D LF LG LM LP) (max (LG * D) LM)

theorem norm_coframe_fixedGenerator_sub_le
    (k : Vec3) {F F₀ G G₀ M M₀ : Vec3 →L[ℝ] Vec3} {D LF LG LM LP d : ℝ}
    (hD : 0 ≤ D)
    (hF : ‖F‖ ≤ D) (hG₀ : ‖G₀‖ ≤ D) (hM : ‖M‖ ≤ D) (hM₀ : ‖M₀‖ ≤ D)
    (hFdiff : ‖F - F₀‖ ≤ LF * d) (hGdiff : ‖G - G₀‖ ≤ LG * d)
    (hMdiff : ‖M - M₀‖ ≤ LM * d)
    (hPdiff : ‖oscillatoryTransverseProjection (G.adjoint k) -
      oscillatoryTransverseProjection (G₀.adjoint k)‖ ≤ LP * d) :
    ‖fixedTransverseGenerator M (coframeLift k F) (coframePullback k G) -
      fixedTransverseGenerator M₀ (coframeLift k F₀) (coframePullback k G₀)‖ ≤
        generatorLabelSlope D LF LG LM LP * d := by
  have hp : ‖coframePullback k G - coframePullback k G₀‖ ≤ (LG + D * LP) * d := by
    refine (norm_coframePullback_sub_le k G G₀).trans ((add_le_add hGdiff
      (mul_le_mul hG₀ hPdiff (norm_nonneg _) hD)).trans_eq ?_)
    ring
  have hf := (norm_coframeLift_sub_le k F F₀).trans hFdiff
  have h := norm_fixedTransverseGenerator_sub_le (J₀ := coframeLift k F₀)
    (R := coframePullback k G) hD hM hM₀
    ((norm_coframeLift_le k F).trans hF) ((norm_coframePullback_le k G₀).trans hG₀)
  refine h.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add hf hp) hMdiff)
    (by positivity)).trans_eq ?_)
  dsimp only [generatorLabelSlope]
  ring

/-- The center covector has a nonzero length and controls the launch covector. -/
theorem coframe_covector_nonzero_and_norm_le (k : Vec3) (hk : k ≠ 0)
    {F G : Vec3 →L[ℝ] Vec3} {D : ℝ}
    (hGF : G.comp F = .id ℝ Vec3) (hF : ‖F‖ ≤ D) :
    G.adjoint k ≠ 0 ∧ ‖k‖ ≤ D * ‖G.adjoint k‖ := by
  have hAdj : F.adjoint (G.adjoint k) = k := by
    change (F.adjoint.comp G.adjoint) k = k
    rw [← adjoint_comp, hGF, adjoint_id, ContinuousLinearMap.id_apply]
  constructor
  · intro h
    have heq : (0 : Vec3) = k := by rwa [h, map_zero] at hAdj
    exact hk heq.symm
  · calc
      ‖k‖ = ‖F.adjoint (G.adjoint k)‖ := by rw [hAdj]
      _ ≤ ‖F.adjoint‖ * ‖G.adjoint k‖ := F.adjoint.le_opNorm _
      _ ≤ D * ‖G.adjoint k‖ := by
        rw [LinearIsometryEquiv.norm_map]
        exact mul_le_mul_of_nonneg_right hF (norm_nonneg _)


/-- The spatially localized seed with projected activation data and the
quantitative conclusions of (5.22). -/
structure SeedOn (M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3) (κ : ℝ → Vec3 → Vec3)
    (center : ℝ → Vec3) (t₀ T ell D C : ℝ) where
  amplitude : ℝ → Vec3 → Vec3
  at_center : EqOn (fun t => amplitude t 0) center (Icc t₀ T)
  activation : ∀ a, amplitude t₀ a = oscillatoryTransverseProjection (κ t₀ a) (center t₀)
  equation : ∀ a t, t ∈ Icc t₀ T → HasDerivWithinAt (fun u => amplitude u a)
    (affineWaveAmplitudeOperator (M t a) (κ t a) (amplitude t a)) (Icc t₀ T) t
  transverse : ∀ a t, t ∈ Icc t₀ T → ⟪κ t a, amplitude t a⟫_ℝ = 0
  near : ∀ a, ‖a‖ ≤ 2 * ell → ∀ t ∈ Icc t₀ T,
    ‖amplitude t a - center t‖ ≤ C * ‖a‖ * ‖center t‖ ∧
    (‖center t‖ / 2 ≤ ‖amplitude t a‖ ∧ ‖amplitude t a‖ ≤ 2 * ‖center t‖) ∧
    (2 * D)⁻¹ * (‖κ t 0‖ * ‖center t‖) ≤ ⟪κ t a, M t a (amplitude t a)⟫_ℝ ∧
    0 < ⟪κ t a, M t a (amplitude t a)⟫_ℝ ∧
    (8 * D)⁻¹ ≤ ⟪κ t a, M t a (amplitude t a)⟫_ℝ / (‖κ t a‖ * ‖amplitude t a‖)

/-- Duhamel in the fixed transverse plane constructs and controls the same
physical seed as the original moving-plane equation. -/
theorem exists_seedOn_of_coframe_bounds
    {F G M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {center : ℝ → Vec3}
    {k : Vec3} {t₀ T D ell LF LG LM LP : ℝ}
    (hk : k ≠ 0) (hT : t₀ ≤ T) (hT₁ : T - t₀ ≤ 1) (hD : 1 ≤ D)
    (hF : ∀ a t, t ∈ Icc t₀ T →
      HasDerivWithinAt (fun u => F u a) ((M t a).comp (F t a)) (Icc t₀ T) t)
    (hG : ∀ a, ContinuousOn (fun t => G t a) (Icc t₀ T))
    (hM : ∀ a, ContinuousOn (fun t => M t a) (Icc t₀ T))
    (hInv : ∀ a t, t ∈ Icc t₀ T →
      (G t a).comp (F t a) = .id ℝ Vec3 ∧ (F t a).comp (G t a) = .id ℝ Vec3)
    (hNorm : ∀ a t, t ∈ Icc t₀ T → ‖F t a‖ ≤ D ∧ ‖G t a‖ ≤ D ∧ ‖M t a‖ ≤ D)
    (hLip : ∀ a t, t ∈ Icc t₀ T →
      ‖F t a - F t 0‖ ≤ LF * ‖a‖ ∧ ‖G t a - G t 0‖ ≤ LG * ‖a‖ ∧
      ‖M t a - M t 0‖ ≤ LM * ‖a‖ ∧
      ‖oscillatoryTransverseProjection ((G t a).adjoint k) -
        oscillatoryTransverseProjection ((G t 0).adjoint k)‖ ≤ LP * ‖a‖)
    (hL : 0 ≤ LF ∧ 0 ≤ LG ∧ 0 ≤ LM ∧ 0 ≤ LP)
    (hCenter : ∀ t ∈ Icc t₀ T, center t ≠ 0 ∧
      ⟪(G t 0).adjoint k, center t⟫_ℝ = 0 ∧
      HasDerivWithinAt center
        (affineWaveAmplitudeOperator (M t 0) ((G t 0).adjoint k) (center t)) (Icc t₀ T) t)
    (hStable : ∀ z : ℝ → Vec3,
      (∀ t ∈ Icc t₀ T, HasDerivWithinAt z
        (affineWaveAmplitudeOperator (M t 0) ((G t 0).adjoint k) (z t)) (Icc t₀ T) t) →
      (∀ t ∈ Icc t₀ T, ⟪(G t 0).adjoint k, z t⟫_ℝ = 0) →
      ∀ {u v : ℝ}, u ∈ Icc t₀ T → v ∈ Icc t₀ T → u ≤ v →
        ‖z v‖ / ‖center v‖ ≤ D * (‖z u‖ / ‖center u‖))
    (hCoupling : ∀ t ∈ Icc t₀ T,
      D⁻¹ * (‖(G t 0).adjoint k‖ * ‖center t‖) ≤ ⟪(G t 0).adjoint k, M t 0 (center t)⟫_ℝ)
    (hSmall : D ^ 3 * generatorLabelSlope D LF LG LM LP * (2 * ell) ≤ 1)
    (hNear : nearLabelSlope D LF LG LM LP * (2 * ell) ≤ (8 * D ^ 2)⁻¹) :
    Nonempty (SeedOn M (fun t a => (G t a).adjoint k) center t₀ T ell D
      (amplitudeLabelSlope D LF LG LM LP)) := by
  let κ (t : ℝ) (a : Vec3) := (G t a).adjoint k
  let J (t : ℝ) (a : Vec3) := coframeLift k (F t a)
  let R (t : ℝ) (a : Vec3) := coframePullback k (G t a)
  let A (t : ℝ) (a : Vec3) := fixedTransverseGenerator (M t a) (J t a) (R t a)
  let g (t : ℝ) := ‖center t‖
  let K : ℝ := D ^ 3
  let LA := generatorLabelSlope D LF LG LM LP
  let LR := LG + D * LP
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hLJ : 0 ≤ LF := hL.1
  have hLG : 0 ≤ LG := hL.2.1
  have hLM : 0 ≤ LM := hL.2.2.1
  have hLP : 0 ≤ LP := hL.2.2.2
  have hLA : 0 ≤ LA := by dsimp only [LA, generatorLabelSlope]; positivity
  have hLR : 0 ≤ LR := by dsimp only [LR]; positivity
  have ht₀ : t₀ ∈ Icc t₀ T := left_mem_Icc.mpr hT
  have hn (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      κ t a ≠ 0 ∧ ‖k‖ ≤ D * ‖κ t a‖ :=
    coframe_covector_nonzero_and_norm_le k hk (hInv a t ht).1 (hNorm a t ht).1
  have hκc (a : Vec3) : ContinuousOn (fun t => κ t a) (Icc t₀ T) := by
    have hAdj := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).continuous
    exact (hAdj.comp_continuousOn (hG a)).clm_apply continuousOn_const
  have hId (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      (R t a).comp (J t a) = .id ℝ (transversePlane k) ∧
      (J t a).comp (R t a) = oscillatoryTransverseProjection (κ t a) :=
    coframe_identities k (hInv a t ht).1 (hInv a t ht).2
  have hJ (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      HasDerivWithinAt (fun u => J u a) ((M t a).comp (J t a)) (Icc t₀ T) t :=
    coframeLift_hasDerivWithinAt k (F := fun u => F u a) (M := fun u => M u a) (hF a t ht)
  have hJnorm (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) : ‖J t a‖ ≤ D :=
    (norm_coframeLift_le k _).trans (hNorm a t ht).1
  have hRnorm (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) : ‖R t a‖ ≤ D :=
    (norm_coframePullback_le k _).trans (hNorm a t ht).2.1
  have hAc (a : Vec3) : ContinuousOn (fun t => A t a) (Icc t₀ T) :=
    continuousOn_fixedTransverseGenerator (hM a) (HasDerivWithinAt.continuousOn (hJ a))
      (coframePullback_continuousOn k (hG a) (fun t ht => (hn a t ht).1))
  have hChange (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      ‖A t a - A t 0‖ ≤ LA * ‖a‖ := by
    obtain ⟨hFa, hGa, hMa, hPa⟩ := hLip a t ht
    exact norm_coframe_fixedGenerator_sub_le k hD₀
      (hNorm a t ht).1 (hNorm 0 t ht).2.1 (hNorm a t ht).2.2 (hNorm 0 t ht).2.2
      hFa hGa hMa hPa
  have hPhysical (a : Vec3) : ContinuousOn
      (fun t => affineWaveAmplitudeOperator (M t a) (κ t a)) (Icc t₀ T) :=
    continuousOn_affineWaveAmplitudeOperator (hM a) (hκc a) (fun t ht => (hn a t ht).1)
  have hgc (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < g t := norm_pos_iff.mpr (hCenter t ht).1
  have hdCenter (t : ℝ) (ht : t ∈ Icc t₀ T) :
      HasDerivWithinAt center (affineWaveAmplitudeOperator (M t 0) (κ t 0) (center t))
        (Icc t₀ T) t := (hCenter t ht).2.2
  obtain ⟨dg, hdg, hg⟩ := norm_hasContinuous_derivative hdCenter
    ((hPhysical 0).clm_apply (HasDerivWithinAt.continuousOn hdCenter))
    (fun t ht => (hCenter t ht).1)
  have hStable' (z : ℝ → transversePlane k)
      (hz : ∀ t ∈ Icc t₀ T, HasDerivWithinAt z (A t 0 (z t)) (Icc t₀ T) t)
      (u : ℝ) (hu : u ∈ Icc t₀ T) (v : ℝ) (hv : v ∈ Icc u T) :
      ‖z v‖ / g v ≤ K * (‖z u‖ / g u) := by
    have hv' : v ∈ Icc t₀ T := ⟨hu.1.trans hv.1, hv.2⟩
    have h := weighted_fixedTransverse_forward hD₀ hD₀ (fun t ht => (hn 0 t ht).1)
      hgc (fun t ht => (hId 0 t ht).1) (fun t ht => (hId 0 t ht).2)
      (hJ 0) (hJnorm 0) (hRnorm 0) hStable z hz hu hv' hv.1
    simpa only [K, show D ^ 3 = D * D * D by ring] using h
  have hexists (a : Vec3) : ∃ z : ℝ → transversePlane k,
      z t₀ = R t₀ a (center t₀) ∧
      ∀ t ∈ Icc t₀ T, HasDerivWithinAt z (A t a (z t)) (Icc t₀ T) t :=
    linearODE_exists_Icc_of_mem ht₀ (hAc a) (R t₀ a (center t₀))
  choose x hx₀ hx using hexists
  let V (t : ℝ) (a : Vec3) := J t a (x a t)
  have hV (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      HasDerivWithinAt (fun u => V u a) (affineWaveAmplitudeOperator (M t a) (κ t a) (V t a))
        (Icc t₀ T) t :=
    hasDerivWithinAt_fixedTransverse_lift (hId a t ht).2 (hJ a t ht) (hx a t ht)
  have hV₀ (a : Vec3) : V t₀ a = oscillatoryTransverseProjection (κ t₀ a) (center t₀) := by
    change J t₀ a (x a t₀) = _
    rw [hx₀ a]
    exact DFunLike.congr_fun (hId a t₀ ht₀).2 (center t₀)
  have hVCenter : EqOn (fun t => V t 0) center (Icc t₀ T) := by
    apply linearODE_unique_of_mem ordConnected_Icc ht₀ (hPhysical 0) (hV 0) hdCenter
    rw [hV₀, oscillatoryTransverseProjection_apply, (hCenter t₀ ht₀).2.1, zero_div,
      zero_smul, sub_zero]
  refine ⟨⟨V, hVCenter, hV₀, hV, fun a t ht => ?_, fun a ha t ht => ?_⟩⟩
  · exact inner_fixedTransverse_lift_eq_zero (hn a t ht).1 (hId a t ht).1 (hId a t ht).2 (x a t)
  · have hd : 0 ≤ LA * ‖a‖ := mul_nonneg hLA (norm_nonneg _)
    have hSmall' : K * (LA * ‖a‖) ≤ 1 := by
      rw [← mul_assoc]
      exact (mul_le_mul_of_nonneg_left ha (mul_nonneg hK hLA)).trans hSmall
    have herr := weighted_near_label_difference_norm_le hK hd hT₁ hSmall'
      (hAc 0) (hAc a) (hChange a) hgc hg hdg hStable' (hx a) (hx 0) ht
    have hInit : ‖x a t₀‖ / g t₀ ≤ D := by
      rw [hx₀ a]
      exact (div_le_iff₀ (hgc t₀ ht₀)).mpr ((R t₀ a).le_of_opNorm_le (hRnorm a t₀ ht₀) _)
    have hΔ : ‖x a t₀ - x 0 t₀‖ / g t₀ ≤ LR * ‖a‖ := by
      rw [hx₀ a, hx₀ 0, ← sub_apply]
      apply (div_le_iff₀ (hgc t₀ ht₀)).mpr
      obtain ⟨_, hGa, _, hPa⟩ := hLip a t₀ ht₀
      have hRΔ : ‖R t₀ a - R t₀ 0‖ ≤ LR * ‖a‖ := by
        refine (norm_coframePullback_sub_le k _ _).trans
          ((add_le_add hGa (mul_le_mul (hNorm 0 t₀ ht₀).2.1 hPa (norm_nonneg _) hD₀)).trans_eq ?_)
        dsimp only [LR]
        ring
      exact (R t₀ a - R t₀ 0).le_of_opNorm_le hRΔ (center t₀)
    have hCoord : ‖x a t - x 0 t‖ ≤
        (K * LR + Real.exp 1 * K ^ 2 * D * LA) * ‖a‖ * g t := by
      apply (div_le_iff₀ (hgc t ht)).mp
      calc
        _ ≤ K * (‖x a t₀ - x 0 t₀‖ / g t₀) +
            Real.exp 1 * K ^ 2 * (‖x a t₀‖ / g t₀) * (LA * ‖a‖) := herr
        _ ≤ K * (LR * ‖a‖) + Real.exp 1 * K ^ 2 * D * (LA * ‖a‖) :=
          add_le_add (mul_le_mul_of_nonneg_left hΔ hK) (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hInit (by positivity)) hd)
        _ = _ := by ring
    have hy : ‖x 0 t‖ ≤ D * g t := by
      have h := DFunLike.congr_fun (hId 0 t ht).1 (x 0 t)
      change R t 0 (V t 0) = x 0 t at h
      rw [show V t 0 = center t from hVCenter ht] at h
      rw [← h]
      exact (R t 0).le_of_opNorm_le (hRnorm 0 t ht) (center t)
    have hPhysicalErr : ‖V t a - center t‖ ≤ amplitudeLabelSlope D LF LG LM LP * ‖a‖ * g t := by
      rw [← (show V t 0 = center t from hVCenter ht)]
      exact physical_error_le_of_coordinates (hJnorm a t ht)
        ((norm_coframeLift_sub_le k _ _).trans (hLip a t ht).1) hy hCoord
    let L := nearLabelSlope D LF LG LM LP
    let δ := L * ‖a‖
    have hLe₁ : amplitudeLabelSlope D LF LG LM LP ≤ L := le_max_left _ _
    have hLe₂ : LG * D ≤ L := (le_max_left _ _).trans (le_max_right _ _)
    have hLe₃ : LM ≤ L := (le_max_right _ _).trans (le_max_right _ _)
    have hL₀ : 0 ≤ L := hLM.trans hLe₃
    have hδ : δ ≤ (8 * D ^ 2)⁻¹ :=
      (mul_le_mul_of_nonneg_left ha hL₀).trans hNear
    have hKΔ : ‖κ t a - κ t 0‖ ≤ δ * ‖κ t 0‖ :=
      (norm_relative_covector_error_le (hLip a t ht).2.1 (hn 0 t ht).2).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLe₂ (norm_nonneg _)) (norm_nonneg _))
    have hVΔ : ‖V t a - center t‖ ≤ δ * g t := hPhysicalErr.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLe₁ (norm_nonneg _)) (norm_nonneg _))
    have hMΔ : ‖M t a - M t 0‖ ≤ δ := (hLip a t ht).2.2.1.trans
      (mul_le_mul_of_nonneg_right hLe₃ (norm_nonneg _))
    obtain ⟨hSpeed, _, hRaw, hPos, hNu⟩ := localized_coupling_positive hD
      (mul_nonneg hL₀ (norm_nonneg _)) hδ (hNorm a t ht).2.2
      (norm_pos_iff.mpr (hn 0 t ht).1) (hgc t ht) hKΔ hVΔ hMΔ (hCoupling t ht)
    exact ⟨hPhysicalErr, hSpeed, hRaw, hPos, hNu⟩


/-- One absolute envelope exponent enforces both the fixed-coordinate
Duhamel perturbation budget and the physical coupling budget. -/
theorem exists_common_envelope_exponent (c : ℝ) (hc : 0 ≤ c) :
    ∃ A : ℕ, 3 ≤ A ∧ ∀ {D ell : ℝ}, 2 ≤ D → 0 ≤ ell → ell ≤ (D ^ A)⁻¹ →
      let L := c * D ^ 24
      D ^ 3 * generatorLabelSlope D L L L L * (2 * ell) ≤ 1 ∧
        nearLabelSlope D L L L L * (2 * ell) ≤ (8 * D ^ 2)⁻¹ := by
  let C := (11 + 8 * Real.exp 1) * c
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨A, hA, hRadius⟩ := exists_envelopeExponent_for_label_error C (1 / 8)
    hC (by norm_num) 35 2
  refine ⟨A, hA, ?_⟩
  intro D ell hD hell hEll
  let L := c * D ^ 24
  let g := generatorLabelSlope D L L L L
  let a := amplitudeLabelSlope D L L L L
  let n := nearLabelSlope D L L L L
  change D ^ 3 * g * (2 * ell) ≤ 1 ∧ n * (2 * ell) ≤ (8 * D ^ 2)⁻¹
  have hD₀ : 0 ≤ D := by linarith
  have hD₁ : 1 ≤ D := by linarith
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hLd : L ≤ D * L := le_mul_of_one_le_left hL hD₁
  have hG : g ≤ 8 * D ^ 3 * L := by
    dsimp only [g, generatorLabelSlope]
    have h := show L + (L + D * L) + L ≤ 4 * (D * L) by linarith
    exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * D ^ 2)).trans_eq (by ring)
  have hD5 : D ^ 5 ≤ D ^ 11 := pow_le_pow_right₀ hD₁ (by norm_num)
  have hD6 : D ^ 6 ≤ D ^ 11 := pow_le_pow_right₀ hD₁ (by norm_num)
  have hD11 : D ≤ D ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ hD₁ (show (1 : ℕ) ≤ 11 by norm_num)
  have hDL : D * L ≤ D ^ 11 * L := mul_le_mul_of_nonneg_right hD11 hL
  have hBase : 0 ≤ D ^ 11 * L := by positivity
  have hAmp : a ≤ (3 + 8 * Real.exp 1) * (D ^ 11 * L) := by
    have h1 : D ^ 3 * (L + D * L) ≤ D ^ 3 * (2 * (D * L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hD₀ _)
    have h2 : Real.exp 1 * (D ^ 3) ^ 2 * D * g ≤
        Real.exp 1 * (D ^ 3) ^ 2 * D * (8 * D ^ 3 * L) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    calc
      a ≤ D * (D ^ 3 * (2 * (D * L)) +
          Real.exp 1 * (D ^ 3) ^ 2 * D * (8 * D ^ 3 * L)) + L * D := by
        dsimp only [a, amplitudeLabelSlope, g]
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hD₀) le_rfl
      _ = 2 * (D ^ 5 * L) + 8 * Real.exp 1 * (D ^ 11 * L) + D * L := by ring
      _ ≤ 2 * (D ^ 11 * L) + 8 * Real.exp 1 * (D ^ 11 * L) + D ^ 11 * L := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hD5 hL) (by norm_num)) le_rfl) hDL
      _ = (3 + 8 * Real.exp 1) * (D ^ 11 * L) := by ring
  have hCoeff : (11 + 8 * Real.exp 1) * (D ^ 11 * L) = C * D ^ 35 := by
    dsimp only [C, L]
    ring
  have hFgen : D ^ 3 * g ≤ C * D ^ 35 := by
    rw [← hCoeff]
    calc
      _ ≤ D ^ 3 * (8 * D ^ 3 * L) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = 8 * (D ^ 6 * L) := by ring
      _ ≤ 8 * (D ^ 11 * L) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hD6 hL) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos 1]) hBase
  have hFnear : n ≤ C * D ^ 35 := by
    rw [← hCoeff]
    dsimp only [n, nearLabelSlope]
    refine max_le (hAmp.trans (mul_le_mul_of_nonneg_right (by linarith) hBase)) ?_
    have hUpper : D ^ 11 * L ≤ (11 + 8 * Real.exp 1) * (D ^ 11 * L) :=
      le_mul_of_one_le_left hBase (by linarith [Real.exp_pos 1])
    have hLD : L * D ≤ D ^ 11 * L := by simpa only [mul_comm L D] using hDL
    exact max_le (hLD.trans hUpper) ((hLd.trans hDL).trans hUpper)
  have hr := hRadius hD hEll
  have hReq : (1 / 8 : ℝ) * (D ^ 2)⁻¹ = (8 * D ^ 2)⁻¹ := by field_simp
  rw [hReq] at hr
  have hInv : (8 * D ^ 2)⁻¹ ≤ 1 := by
    have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD₁
    simpa only [inv_one] using inv_anti₀ (show (0 : ℝ) < 1 by norm_num)
      (show 1 ≤ 8 * D ^ 2 by linarith)
  exact ⟨((mul_le_mul_of_nonneg_right hFgen (by positivity)).trans hr).trans hInv,
    (mul_le_mul_of_nonneg_right hFnear (by positivity)).trans hr⟩

private theorem continuousOn_inverse_coframe
    {F G : ℝ → Vec3 →L[ℝ] Vec3} {I : Set ℝ} {D : ℝ}
    (hD : 0 < D) (hF : ContinuousOn F I)
    (hGF : ∀ t ∈ I, (G t).comp (F t) = .id ℝ Vec3)
    (hFG : ∀ t ∈ I, (F t).comp (G t) = .id ℝ Vec3)
    (hG : ∀ t ∈ I, ‖G t‖ ≤ D) : ContinuousOn G I := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hDsq : 0 < D ^ 2 := sq_pos_of_pos hD
  obtain ⟨δ, hδ, hFδ⟩ := Metric.continuousWithinAt_iff.mp (hF t ht)
    (ε / D ^ 2) (div_pos hε hDsq)
  refine ⟨δ, hδ, fun u hu hud => ?_⟩
  have heq : G u - G t = (G u).comp ((F t - F u).comp (G t)) := by
    apply ContinuousLinearMap.ext
    intro x
    change G u x - G t x = G u ((F t - F u) (G t x))
    have htu : F t (G t x) = x := DFunLike.congr_fun (hFG t ht) x
    have hut : G u (F u (G t x)) = G t x := DFunLike.congr_fun (hGF u hu) (G t x)
    rw [sub_apply, map_sub, htu, hut]
  have hnorm : ‖G u - G t‖ ≤ D ^ 2 * ‖F u - F t‖ := by
    rw [heq]
    calc
      _ ≤ ‖G u‖ * (‖F t - F u‖ * ‖G t‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ D * (‖F t - F u‖ * D) :=
        mul_le_mul (hG u hu) (mul_le_mul_of_nonneg_left (hG t ht) (norm_nonneg _))
          (by positivity) hD.le
      _ = _ := by rw [norm_sub_rev (F u) (F t)]; ring
  have h := hFδ hu hud
  rw [dist_eq_norm] at h ⊢
  exact hnorm.trans_lt ((mul_lt_mul_of_pos_left h hDsq).trans_eq
    (by field_simp))

/-- Data at the actual parent center used by the localized seed proof. -/
structure CenterWaveOn (M : ℝ → Vec3 →L[ℝ] Vec3) (κ center : ℝ → Vec3)
    (t₀ T D : ℝ) : Prop where
  covector : ∀ t ∈ Icc t₀ T, HasDerivWithinAt κ (-((M t).adjoint (κ t))) (Icc t₀ T) t
  nonzero : ∀ t ∈ Icc t₀ T, κ t ≠ 0 ∧ center t ≠ 0 ∧ ⟪κ t, center t⟫_ℝ = 0
  amplitude : ∀ t ∈ Icc t₀ T, HasDerivWithinAt center
    (affineWaveAmplitudeOperator (M t) (κ t) (center t)) (Icc t₀ T) t
  stability : ∀ z : ℝ → Vec3,
    (∀ t ∈ Icc t₀ T, HasDerivWithinAt z (affineWaveAmplitudeOperator (M t) (κ t) (z t))
      (Icc t₀ T) t) →
    (∀ t ∈ Icc t₀ T, ⟪κ t, z t⟫_ℝ = 0) →
      ∀ {u v : ℝ}, u ∈ Icc t₀ T → v ∈ Icc t₀ T → u ≤ v →
        ‖z v‖ / ‖center v‖ ≤ D * (‖z u‖ / ‖center u‖)
  coupling : ∀ t ∈ Icc t₀ T, D⁻¹ * (‖κ t‖ * ‖center t‖) ≤ ⟪κ t, M t (center t)⟫_ℝ

/-- The first central wave supplies the data for the actual parent coframe
comparison. -/
theorem firstWave_centerWaveOn {s T freq D : ℝ} (w : FirstWaveOrigin s T freq)
    (hf : 0 < freq) (hs : |s| ≤ 1)
    (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) (hD : 2 ≤ D) :
    CenterWaveOn (fun _ => stationaryShearGradient s) w.covector w.amplitude 0 T D := by
  obtain ⟨hforward, hcoupling⟩ := w.localized_center_estimates hf hs hsmall hD
  exact ⟨w.covector_equation, w.transverse, w.amplitude_equation,
    fun z hz _ u v hu hv huv => hforward z hz hu hv huv, hcoupling⟩

/-- Transport center data across an exact equality with the parent's
central gradient on the physical slab. -/
theorem CenterWaveOn.congr_gradient
    {M N : ℝ → Vec3 →L[ℝ] Vec3} {κ center : ℝ → Vec3} {t₀ T D : ℝ}
    (h : CenterWaveOn M κ center t₀ T D) (hEq : EqOn M N (Icc t₀ T)) :
    CenterWaveOn N κ center t₀ T D := by
  refine ⟨fun t ht => ?_, h.nonzero, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · rw [← hEq ht]
    exact h.covector t ht
  · rw [← hEq ht]
    exact h.amplitude t ht
  · intro z hz hperp u v hu hv huv
    refine h.stability z (fun t ht => ?_) hperp hu hv huv
    rw [hEq ht]
    exact hz t ht
  · rw [← hEq ht]
    exact h.coupling t ht

/-- The first-wave center data use the actual gradient of the stationary
parent at the origin. -/
theorem firstWave_parentCenterWaveOn {s T freq D : ℝ} (w : FirstWaveOrigin s T freq)
    (hf : 0 < freq) (hs : |s| ≤ 1)
    (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) (hD : 2 ≤ D) :
    CenterWaveOn (fun _ => fderiv ℝ (stationaryShear s) 0)
      w.covector w.amplitude 0 T D := by
  exact (firstWave_centerWaveOn w hf hs hsmall hD).congr_gradient
    (fun _ _ => (stationaryShearGradient_origin s).symm)

/-- Every supplied growing crossing obeying the physical threshold supplies
the center data for the later-wave localization. -/
theorem exists_laterWave_centerWaveOn_threshold :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
        ∀ (w : MovingWaveVector.PhysicalAmplification I t₀)
          (d : w.GrowingCrossing T scale Ustar next),
          2 ≤ T → scale ≠ 0 → (C₀ : ℝ) * w.ratio ≤ 1 →
          (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
          ∀ D : ℝ, 252 * Real.exp 1 * w.shear ≤ D → 2 / (w.firstCoupling * w.ratio) ≤ D →
            CenterWaveOn w.gradient d.waveVector d.amplitude t₀ (w.clock T) D := by
  obtain ⟨N, hN, hd⟩ :=
    MovingWaveVector.PhysicalAmplification.exists_localized_center_estimates_threshold
  refine ⟨N, hN, ?_⟩
  intro I t₀ T scale Ustar next C₀ hC₀ w d hT hscale hε hδ D hGrow hν
  obtain ⟨hforward, hcoupling⟩ := hd hC₀ w d hT hscale hε hδ D hGrow hν
  exact ⟨d.waveVector_derivative, d.transverse, d.amplitude_derivative, hforward, hcoupling⟩

/-- The actual parent coframe, material gradient and transported covector
supply the localized seed. The launch covector is recovered from the
prescribed one at activation. -/
theorem exists_seedOn_of_parent_bounds (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ 3 ≤ A ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ell : ℝ} {κ center : ℝ → Vec3},
        0 < T → T ≤ 1 → t₀ ∈ Icc 0 T → 2 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, Function.Odd (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ D) →
        (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
        CenterWaveOn (fun t => fderiv ℝ (U t) 0) κ center t₀ T D →
        let L := C * D ^ 24
        let k := (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (κ t₀)
        0 < ell → ell ≤ (D ^ A)⁻¹ →
        Nonempty (SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
          (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D
          (amplitudeLabelSlope D L L L L)) := by
  obtain ⟨C, hC, hLip⟩ := exists_parent_coefficient_label_lipschitz R hR
  obtain ⟨A, hA, hRadius⟩ := exists_common_envelope_exponent C hC
  refine ⟨C, A, hC, hA, ?_⟩
  intro U X T t₀ D ell κ center hT hT₁ ht₀ hD hX hU hper hodd hF hG hM hUjet hCenter
  dsimp only
  intro hell hellA
  obtain ⟨hSmall, hNear⟩ := hRadius hD hell.le hellA
  let k := (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (κ t₀)
  let L := C * D ^ 24
  let F (t : ℝ) (a : Vec3) := fderiv ℝ (X 0 t) a
  let G (t : ℝ) (a : Vec3) := fderiv ℝ (X t 0) (X 0 t a)
  let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
  have hDone : 1 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hL₀ : 0 ≤ L := by dsimp only [L]; positivity
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hStart : t₀ ∈ Icc t₀ T := left_mem_Icc.mpr ht₀.2
  have hsub : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀.1
  obtain ⟨Lp, hLp⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU₂.of_le (by norm_num)) hper
  have hFix (t : ℝ) (ht : t ∈ Icc 0 T) : X 0 t (0 : Vec3) = 0 := by
    have he := hX.odd hLp hodd h₀ ht (0 : Vec3)
    rw [neg_zero] at he
    ext i
    have hi := congrArg (fun y : Vec3 => y i) he
    simp only [PiLp.neg_apply] at hi
    simpa only [PiLp.zero_apply] using (show (X 0 t 0) i = 0 by linarith)
  have hMzero (t : ℝ) (ht : t ∈ Icc t₀ T) : M t 0 = fderiv ℝ (U t) 0 := by
    simp only [M, hFix t (hsub ht)]
  obtain ⟨hknz, hkc⟩ := hX.center_coframe_covector_eq hT hU₂ hper hodd ht₀ hCenter.covector
  have hk : k ≠ 0 := hknz (hCenter.nonzero t₀ hStart).1
  have hkeq (t : ℝ) (ht : t ∈ Icc t₀ T) : (G t 0).adjoint k = κ t := by
    simpa only [G, hFix t (hsub ht)] using hkc t ht
  have hΛ : 0 < ‖κ t₀‖ := norm_pos_iff.mpr (hCenter.nonzero t₀ hStart).1
  have hFreq : ‖labelWaveVector X 0 0 k t₀‖ = ‖κ t₀‖ :=
    congrArg norm (hkeq t₀ hStart)
  have hFder (a : Vec3) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => F u a) ((M t a).comp (F t a)) (Icc 0 T) t :=
    (hX.labelDerivative_evolves hT hU₂ hper h₀ a).2 t ht
  have hInv (a : Vec3) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (G t a).comp (F t a) = .id ℝ Vec3 ∧ (F t a).comp (G t a) = .id ℝ Vec3 :=
    hX.labelDerivative_inverse hT hU₂ hper h₀ ht a
  have hGtime (a : Vec3) : ContinuousOn (fun t => G t a) (Icc 0 T) :=
    continuousOn_inverse_coframe hDpos (HasDerivWithinAt.continuousOn (hFder a))
      (fun t ht => (hInv a t ht).1) (fun t ht => (hInv a t ht).2)
      (fun t ht => hG t ht a)
  have hMtime (a : Vec3) : ContinuousOn (fun t => M t a) (Icc 0 T) := by
    have hgrad : ContDiffOn ℝ 1 (fun p : ℝ × Vec3 => fderiv ℝ (U p.1) p.2)
        (Icc 0 T ×ˢ univ) :=
      contDiffOn_spatialDerivative_of_joint_contDiff (n := 1) (uniqueDiffOn_Icc hT) (by
        convert hU₂ using 1
        norm_num)
    exact hgrad.continuousOn.comp
      (continuous_id.continuousOn.prodMk (HasDerivWithinAt.continuousOn (hX.trajectory 0 h₀ a)))
      (fun t ht => ⟨ht, mem_univ _⟩)
  have hLC (p : ℕ) (hp : p ≤ 24) (a : Vec3) : C * D ^ p * ‖a‖ ≤ L * ‖a‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hDone hp) hC
  have hLactual (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      ‖F t a - F t 0‖ ≤ L * ‖a‖ ∧ ‖G t a - G t 0‖ ≤ L * ‖a‖ ∧
      ‖M t a - M t 0‖ ≤ L * ‖a‖ ∧
      ‖oscillatoryTransverseProjection ((G t a).adjoint k) -
        oscillatoryTransverseProjection ((G t 0).adjoint k)‖ ≤ L * ‖a‖ := by
    have hc := hLip hT hT₁ hDone hX hU hper hF hG hUjet k hΛ ht₀ hFreq t (hsub ht) a 0
    simp only [sub_zero] at hc
    exact ⟨hc.1.trans (hLC 6 (by decide) a), hc.2.1.trans (hLC 8 (by decide) a),
      hc.2.2.1.trans (hLC 7 (by decide) a), hc.2.2.2.2⟩
  have hcBoth (t : ℝ) (ht : t ∈ Icc t₀ T) :
      center t ≠ 0 ∧ ⟪(G t 0).adjoint k, center t⟫_ℝ = 0 ∧
      HasDerivWithinAt center
        (affineWaveAmplitudeOperator (M t 0) ((G t 0).adjoint k) (center t)) (Icc t₀ T) t := by
    rw [hkeq t ht, hMzero t ht]
    exact ⟨(hCenter.nonzero t ht).2.1, (hCenter.nonzero t ht).2.2, hCenter.amplitude t ht⟩
  refine exists_seedOn_of_coframe_bounds hk ht₀.2 (by linarith [ht₀.1]) hDone
    (fun a t ht => (hFder a t (hsub ht)).mono hsub) (fun a => (hGtime a).mono hsub)
    (fun a => (hMtime a).mono hsub) (fun a t ht => hInv a t (hsub ht))
    (fun a t ht => ⟨hF t (hsub ht) a, hG t (hsub ht) a, hM t (hsub ht) (X 0 t a)⟩)
    hLactual ⟨hL₀, hL₀, hL₀, hL₀⟩ hcBoth ?_ ?_ hSmall hNear
  · intro z hz hp u v hu hv huv
    refine hCenter.stability z (fun t ht => ?_) (fun t ht => ?_) hu hv huv
    · rw [← hkeq t ht, ← hMzero t ht]
      exact hz t ht
    · rw [← hkeq t ht]
      exact hp t ht
  · intro t ht
    change D⁻¹ * (‖(G t 0).adjoint k‖ * ‖center t‖) ≤
      ⟪(G t 0).adjoint k, M t 0 (center t)⟫_ℝ
    rw [hkeq t ht, hMzero t ht]
    exact hCenter.coupling t ht

/-- The seed produced by the localization theorem supplies the order-zero
leading velocity and pressure bounds in (5.25). -/
theorem SeedOn.weighted_leading_size
    {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3} {center : ℝ → Vec3}
    {t₀ T ell D C t freq chi : ℝ} (w : SeedOn M κ center t₀ T ell D C)
    (ht : t ∈ Icc t₀ T) (hf : 1 ≤ freq) (hell : 0 < ell) (hD : 1 ≤ D)
    (hchi : 0 ≤ chi) (hchi₁ : chi ≤ 1) (hc : center t ≠ 0)
    (hκ : ∀ a, ‖a‖ ≤ 2 * ell → freq ≤ D ^ 2 * ‖κ t a‖)
    (hM : ∀ a, ‖a‖ ≤ 2 * ell → ‖M t a‖ ≤ D) (a : Vec3) (s : ℝ) :
    let γ := freq ^ (3 / 4 : ℝ) * ‖center t‖
    let leading (r : ℝ) :=
      ((chi * radialEnvelope ell a) * waveProfile (freq ^ (-1 / 2 : ℝ)) r) • w.amplitude t a
    ‖leading s‖ / γ ≤ freq ^ (-5 / 4 : ℝ) ∧
      freq * ‖oscillatoryPhasePressure (M t a) (κ t a) (fun _ => 0) leading s‖ / γ ≤
        4 * D ^ 3 * freq ^ (-5 / 4 : ℝ) := by
  have hCenter : w.amplitude t 0 = center t := w.at_center ht
  have h₀ : w.amplitude t 0 ≠ 0 := hCenter.symm ▸ hc
  have hNear (a : Vec3) (ha : ‖a‖ ≤ 2 * ell) : ‖w.amplitude t a‖ ≤ 2 * ‖w.amplitude t 0‖ := by
    rw [hCenter]
    exact (w.near a ha t ht).2.1.2
  have hVelocity := norm_switchedLeadingProfile_div_seedWeight_le hf hell hchi hchi₁ h₀ hNear a s
  have hPressure := freq_mul_norm_switchedLeadingPressure_div_seedWeight_le hf hell hchi hchi₁
    hD h₀ hNear hκ hM a s
  simpa only [hCenter] using And.intro hVelocity hPressure

end TorusEuler.LocalizedAmplitude
