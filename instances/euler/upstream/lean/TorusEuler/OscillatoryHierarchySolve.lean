import TorusEuler.AffinePropagation
import TorusEuler.PhaseCalculus
import TorusEuler.ReferenceComparison
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The forced transverse equation and pressure in (5.16)–(5.17). -/

open Set MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The forcing projection onto the plane perpendicular to the wave vector. -/
noncomputable def oscillatoryTransverseProjection (κ : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (‖κ‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ κ κ

theorem oscillatoryTransverseProjection_apply (κ f : E) :
    oscillatoryTransverseProjection κ f = f - (⟪κ, f⟫_ℝ / ‖κ‖ ^ 2) • κ := by
  simp only [oscillatoryTransverseProjection, sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, InnerProductSpace.rankOne_apply, smul_smul, div_eq_inv_mul]

theorem inner_oscillatoryTransverseProjection (κ f : E) (hκ : κ ≠ 0) :
    ⟪κ, oscillatoryTransverseProjection κ f⟫_ℝ = 0 := by
  rw [oscillatoryTransverseProjection_apply, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hκ)), sub_self]

theorem norm_oscillatoryTransverseProjection_le (κ f : E) (hκ : κ ≠ 0) :
    ‖oscillatoryTransverseProjection κ f‖ ≤ ‖f‖ := by
  let p := oscillatoryTransverseProjection κ f
  let q := (⟪κ, f⟫_ℝ / ‖κ‖ ^ 2) • κ
  have hsum : p + q = f := by
    dsimp only [p, q]
    rw [oscillatoryTransverseProjection_apply, sub_add_cancel]
  have hp : ⟪κ, p⟫_ℝ = 0 := inner_oscillatoryTransverseProjection κ f hκ
  rw [real_inner_comm] at hp
  have hortho : ⟪p, q⟫_ℝ = 0 := by
    dsimp only [q]
    rw [real_inner_smul_right, hp, mul_zero]
  have hnorm := norm_add_sq_eq_norm_sq_add_norm_sq_real hortho
  rw [hsum] at hnorm
  exact le_of_sq_le_sq (by nlinarith [sq_nonneg ‖q‖]) (norm_nonneg f)

theorem continuousOn_oscillatoryTransverseProjection {κ : ℝ → E} {J : Set ℝ}
    (hκ : ContinuousOn κ J) (hκ₀ : ∀ t ∈ J, κ t ≠ 0) :
    ContinuousOn (fun t => oscillatoryTransverseProjection (κ t)) J := by
  have hInner := (innerSL ℝ (E := E)).continuous.comp_continuousOn hκ
  have hRank : ContinuousOn (fun t => InnerProductSpace.rankOne ℝ (κ t) (κ t)) J :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := E) (F := E)).continuous
      |>.comp_continuousOn (hInner.prodMk hκ)
  have hScale := (hκ.norm.pow 2).inv₀
    (fun t ht => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ₀ t ht)))
  exact continuousOn_const.sub (hScale.smul hRank)

/-- The phase derivative of the oscillatory pressure in (5.16). -/
noncomputable def oscillatoryPressureSlope (M : E →L[ℝ] E) (κ f V : E) : ℝ :=
  (⟪κ, f⟫_ℝ - 2 * ⟪κ, M V⟫_ℝ) / ‖κ‖ ^ 2

theorem norm_sq_mul_oscillatoryPressureSlope (M : E →L[ℝ] E) (κ f V : E)
    (hκ : κ ≠ 0) :
    ‖κ‖ ^ 2 * oscillatoryPressureSlope M κ f V = ⟪κ, f⟫_ℝ - 2 * ⟪κ, M V⟫_ℝ := by
  rw [mul_comm, oscillatoryPressureSlope, div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hκ))]

theorem abs_oscillatoryPressureSlope_le (M : E →L[ℝ] E) (κ f V : E) (hκ : κ ≠ 0) :
    |oscillatoryPressureSlope M κ f V| ≤ (‖f‖ + 2 * ‖M‖ * ‖V‖) / ‖κ‖ := by
  have hk := norm_pos_iff.mpr hκ
  have hV : |⟪κ, M V⟫_ℝ| ≤ ‖κ‖ * (‖M‖ * ‖V‖) :=
    (abs_real_inner_le_norm κ (M V)).trans (mul_le_mul_of_nonneg_left (M.le_opNorm V) hk.le)
  rw [oscillatoryPressureSlope, abs_div, abs_of_nonneg (sq_nonneg ‖κ‖)]
  calc
    _ ≤ (|⟪κ, f⟫_ℝ| + 2 * |⟪κ, M V⟫_ℝ|) / ‖κ‖ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        abs_sub (⟪κ, f⟫_ℝ) (2 * ⟪κ, M V⟫_ℝ)
    _ ≤ (‖κ‖ * ‖f‖ + 2 * (‖κ‖ * (‖M‖ * ‖V‖))) / ‖κ‖ ^ 2 :=
      div_le_div_of_nonneg_right
        (add_le_add (abs_real_inner_le_norm κ f) (mul_le_mul_of_nonneg_left hV (by norm_num)))
        (sq_nonneg _)
    _ = _ := by field_simp [hk.ne']

theorem affineWaveAmplitudeOperator_add_transverseProjection
    (M : E →L[ℝ] E) (κ f V : E) :
    affineWaveAmplitudeOperator M κ V + oscillatoryTransverseProjection κ f =
      f - M V - oscillatoryPressureSlope M κ f V • κ := by
  rw [affineWaveAmplitudeOperator_apply, oscillatoryTransverseProjection_apply,
    oscillatoryPressureSlope, sub_div, sub_smul]
  abel

variable [CompleteSpace E]

private theorem hasDerivWithinAt_oscillatoryPairing_zero
    {M : E →L[ℝ] E} {κ V : ℝ → E} {J : Set ℝ} {t : ℝ} {f : E}
    (hκ₀ : κ t ≠ 0) (hκ : HasDerivWithinAt κ (-(M.adjoint (κ t))) J t)
    (hV : HasDerivWithinAt V
      (affineWaveAmplitudeOperator M (κ t) (V t) + oscillatoryTransverseProjection (κ t) f) J t) :
    HasDerivWithinAt (fun r => ⟪κ r, V r⟫_ℝ) 0 J t := by
  refine (hκ.inner ℝ hV).congr_deriv ?_
  rw [inner_neg_left, M.adjoint_inner_left, inner_add_right,
    inner_oscillatoryTransverseProjection _ _ hκ₀, add_zero, affineWaveAmplitudeOperator_apply,
    inner_add_right, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hκ₀))]
  ring

/-- A solution of (5.17) with transverse initial data remains transverse on the
entire interval, including the endpoints. -/
theorem oscillatory_transverse_of_initial {M : ℝ → E →L[ℝ] E} {κ V f : ℝ → E}
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hκ₀ : ∀ t ∈ J, κ t ≠ 0)
    (hκ : ∀ t ∈ J, HasDerivWithinAt κ (-((M t).adjoint (κ t))) J t)
    (hV : ∀ t ∈ J, HasDerivWithinAt V
      (affineWaveAmplitudeOperator (M t) (κ t) (V t) +
        oscillatoryTransverseProjection (κ t) (f t)) J t)
    (hV₀ : ⟪κ t₀, V t₀⟫_ℝ = 0) :
    ∀ t ∈ J, ⟪κ t, V t⟫_ℝ = 0 := by
  have heq : EqOn (fun t => ⟪κ t, V t⟫_ℝ) (fun _ => (0 : ℝ)) J :=
    linearODE_unique_of_mem (A := fun _ => 0) hJ ht₀ continuousOn_const
      (fun t ht => by simpa only [zero_apply] using
        hasDerivWithinAt_oscillatoryPairing_zero (hκ₀ t ht) (hκ t ht) (hV t ht))
      (fun t _ => by simpa only [zero_apply] using hasDerivWithinAt_const t J (0 : ℝ)) hV₀
  exact heq

/-- For every fixed label and phase, continuous coefficients and forcing give
a transverse velocity with the exact pressure slope on the closed time slab. -/
theorem exists_oscillatoryTransverse_Icc {M : ℝ → E →L[ℝ] E} {κ f : ℝ → E}
    {l r t₀ : ℝ} (ht₀ : t₀ ∈ Icc l r) (hM : ContinuousOn M (Icc l r))
    (hκ : ∀ t ∈ Icc l r, HasDerivWithinAt κ (-((M t).adjoint (κ t))) (Icc l r) t)
    (hκ₀ : κ t₀ ≠ 0) (hf : ContinuousOn f (Icc l r))
    (V₀ : E) (hV₀ : ⟪κ t₀, V₀⟫_ℝ = 0) :
    ∃ V : ℝ → E, V t₀ = V₀ ∧ ∀ t ∈ Icc l r,
      κ t ≠ 0 ∧ ⟪κ t, V t⟫_ℝ = 0 ∧
      HasDerivWithinAt V
        (affineWaveAmplitudeOperator (M t) (κ t) (V t) +
          oscillatoryTransverseProjection (κ t) (f t)) (Icc l r) t ∧
      let pₛ := oscillatoryPressureSlope (M t) (κ t) (f t) (V t)
      ‖κ t‖ ^ 2 * pₛ = ⟪κ t, f t⟫_ℝ - 2 * ⟪κ t, M t (V t)⟫_ℝ ∧
      HasDerivWithinAt V (f t - M t (V t) - pₛ • κ t) (Icc l r) t := by
  have hMAdj : ContinuousOn (fun t => -(M t).adjoint) (Icc l r) :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hM).neg
  have hκ_ne : ∀ t ∈ Icc l r, κ t ≠ 0 :=
    linearODE_ne_zero_of_mem ordConnected_Icc ht₀ hMAdj
      (fun t ht => by simpa only [neg_apply] using hκ t ht) hκ₀
  have hκc := HasDerivWithinAt.continuousOn hκ
  obtain ⟨V, hinit, hV⟩ := linearODE_inhom_exists_Icc ht₀
    (continuousOn_affineWaveAmplitudeOperator hM hκc hκ_ne)
    ((continuousOn_oscillatoryTransverseProjection hκc hκ_ne).clm_apply hf) V₀
  have hperp := oscillatory_transverse_of_initial ordConnected_Icc ht₀ hκ_ne hκ hV (hinit ▸ hV₀)
  refine ⟨V, hinit, fun t ht => ⟨hκ_ne t ht, hperp t ht, hV t ht, ?_, ?_⟩⟩
  · exact norm_sq_mul_oscillatoryPressureSlope _ _ _ _ (hκ_ne t ht)
  · simpa only [affineWaveAmplitudeOperator_add_transverseProjection] using hV t ht

/-- A weighted forward estimate on homogeneous transverse paths implies the
order-zero velocity estimate for the forced transverse equation. -/
theorem norm_oscillatoryVelocity_weighted_le
    {M : ℝ → E →L[ℝ] E} {κ V f : ℝ → E} {γ : ℝ → ℝ} {l r t K F : ℝ}
    (ht : t ∈ Icc l r) (hM : ContinuousOn M (Icc l r))
    (hκ : ContinuousOn κ (Icc l r)) (hκ₀ : ∀ u ∈ Icc l r, κ u ≠ 0)
    (hf : ContinuousOn f (Icc l r)) (hγ : ∀ u ∈ Icc l r, 0 < γ u)
    (hK : 0 ≤ K) (hF : ∀ u ∈ Icc l r, ‖f u‖ ≤ γ u * F)
    (hStable : ∀ x : ℝ → E,
      (∀ u ∈ Icc l r, HasDerivWithinAt x
        (affineWaveAmplitudeOperator (M u) (κ u) (x u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ⟪κ u, x u⟫_ℝ = 0 →
      ∀ v ∈ Icc u r, ‖x v‖ ≤ K * (γ v / γ u) * ‖x u‖)
    (hV : ∀ u ∈ Icc l r, HasDerivWithinAt V
      (affineWaveAmplitudeOperator (M u) (κ u) (V u) +
        oscillatoryTransverseProjection (κ u) (f u)) (Icc l r) u)
    (hV₀ : ⟪κ l, V l⟫_ℝ = 0) :
    ‖V t‖ / γ t ≤ K * (‖V l‖ / γ l + (t - l) * F) := by
  let A (u : ℝ) := affineWaveAmplitudeOperator (M u) (κ u)
  let g (u : ℝ) := oscillatoryTransverseProjection (κ u) (f u)
  have hlr := ht.1.trans ht.2
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr⟩
  have hA : ContinuousOn A (Icc l r) := continuousOn_affineWaveAmplitudeOperator hM hκ hκ₀
  have hg : ContinuousOn g (Icc l r) := (continuousOn_oscillatoryTransverseProjection hκ hκ₀).clm_apply hf
  obtain ⟨Φ, hΦ₀, hΦ⟩ := linearODE_exists_Icc (E := E →L[ℝ] E)
    (A := fun u => ContinuousLinearMap.compL ℝ E E E (A u)) hlr
    ((ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hA)
    (ContinuousLinearMap.id ℝ E)
  obtain ⟨Ψ, hΨ₀, hΨ⟩ := linearODE_exists_Icc (E := E →L[ℝ] E)
    (A := fun u => -(ContinuousLinearMap.compL ℝ E E E).flip (A u)) hlr
    (((ContinuousLinearMap.compL ℝ E E E).flip.continuous.comp_continuousOn hA).neg)
    (ContinuousLinearMap.id ℝ E)
  have hΦ' (u : ℝ) (hu : u ∈ Icc l r) :
      HasDerivWithinAt Φ ((A u).comp (Φ u)) (Icc l r) u := hΦ u hu
  have hΨ' (u : ℝ) (hu : u ∈ Icc l r) :
      HasDerivWithinAt Ψ (-((Ψ u).comp (A u))) (Icc l r) u := by
    simpa only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      neg_apply] using hΨ u hu
  have hInv := linearODE_fundamental_comp_inv ordConnected_Icc hl hA hΦ' hΨ' hΦ₀ hΨ₀
  have hPath (v : E) (u : ℝ) (hu : u ∈ Icc l r) :
      HasDerivWithinAt (fun s => Φ s v) (A u (Φ u v)) (Icc l r) u := by
    simpa using (hΦ' u hu).clm_apply (hasDerivWithinAt_const u (Icc l r) v)
  have hInit : ⟪κ l, Φ l (V l)⟫_ℝ = 0 := by simpa [hΦ₀] using hV₀
  have hFirst : ‖Φ t (V l)‖ ≤ K * (γ t / γ l) * ‖V l‖ := by
    simpa [hΦ₀] using hStable (fun s => Φ s (V l)) (hPath (V l)) l hl hInit t ht
  have hKernel (u : ℝ) (hu : u ∈ Icc l t) : ‖Φ t (Ψ u (g u))‖ ≤ K * γ t * F := by
    have hu' : u ∈ Icc l r := ⟨hu.1, hu.2.trans ht.2⟩
    have hpoint : Φ u (Ψ u (g u)) = g u := by
      exact congrArg (fun L : E →L[ℝ] E => L (g u)) (hInv u hu')
    have hperp : ⟪κ u, Φ u (Ψ u (g u))⟫_ℝ = 0 := by
      rw [hpoint]
      exact inner_oscillatoryTransverseProjection _ _ (hκ₀ u hu')
    have hBound := hStable (fun s => Φ s (Ψ u (g u))) (hPath (Ψ u (g u))) u hu'
      hperp t ⟨hu.2, ht.2⟩
    rw [hpoint] at hBound
    calc
      _ ≤ K * (γ t / γ u) * ‖g u‖ := hBound
      _ ≤ K * (γ t / γ u) * (γ u * F) :=
        mul_le_mul_of_nonneg_left ((norm_oscillatoryTransverseProjection_le
          (κ u) (f u) (hκ₀ u hu')).trans (hF u hu'))
          (mul_nonneg hK (div_pos (hγ t ht) (hγ u hu')).le)
      _ = _ := by field_simp [(hγ u hu').ne']
  have hGc : ContinuousOn (fun u => Φ t (Ψ u (g u))) (Icc l t) :=
    (Φ t).continuous.comp_continuousOn
      (((HasDerivWithinAt.continuousOn hΨ').clm_apply hg).mono (Icc_subset_Icc_right ht.2))
  have hI : ‖∫ u in l..t, Φ t (Ψ u (g u))‖ ≤ (t - l) * (K * γ t * F) := by
    calc
      _ ≤ ∫ u in l..t, ‖Φ t (Ψ u (g u))‖ := intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ _ in l..t, K * γ t * F := intervalIntegral.integral_mono_on ht.1
        (hGc.norm.intervalIntegrable_of_Icc ht.1) intervalIntegrable_const hKernel
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hnorm : ‖V t‖ ≤ K * (γ t / γ l) * ‖V l‖ + (t - l) * (K * γ t * F) := by
    rw [linearODE_variation_of_constants hA hg hΦ₀ hΨ₀ hΦ' hΨ' hV ht]
    exact (norm_add_le _ _).trans (add_le_add hFirst hI)
  apply (div_le_iff₀ (hγ t ht)).mpr
  refine hnorm.trans_eq ?_
  ring

/-- The phase pressure is the primitive on the unit period normalized to zero mean. -/
noncomputable def oscillatoryPhasePressure (M : E →L[ℝ] E) (κ : E) (f V : ℝ → E) : ℝ → ℝ :=
  phasePrimitive (fun s => oscillatoryPressureSlope M κ (f s) (V s))

private theorem oscillatory_slope_phase_properties (M : E →L[ℝ] E) (κ : E)
    {f V : ℝ → E} (hf : Continuous f) (hV : Continuous V)
    (hfper : Function.Periodic f 1) (hVper : Function.Periodic V 1)
    (hfmean : phaseMean f = 0) (hVmean : phaseMean V = 0) :
    let q (s : ℝ) := oscillatoryPressureSlope M κ (f s) (V s)
    Continuous q ∧ Function.Periodic q 1 ∧ phaseMean q = 0 := by
  let A := ((‖κ‖ ^ 2)⁻¹ : ℝ) • innerSL ℝ κ
  let B := (2 : ℝ) • A.comp M
  have hEq : (fun s => oscillatoryPressureSlope M κ (f s) (V s)) =
      fun s => A (f s) - B (V s) := by
    funext s
    simp only [oscillatoryPressureSlope, A, B, smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  dsimp only
  rw [hEq]
  have hcF : Continuous (fun s => A (f s)) := A.continuous.comp hf
  have hcV : Continuous (fun s => B (V s)) := B.continuous.comp hV
  refine ⟨hcF.sub hcV, fun s => by simp only [hfper s, hVper s], ?_⟩
  rw [phaseMean_sub hcF hcV]
  have hf' : phaseMean (fun s => A (f s)) = A (phaseMean f) :=
    A.intervalIntegral_comp_comm (hf.intervalIntegrable 0 1)
  have hV' : phaseMean (fun s => B (V s)) = B (phaseMean V) :=
    B.intervalIntegral_comp_comm (hV.intervalIntegrable 0 1)
  simp only [hf', hV', hfmean, hVmean, map_zero, sub_self]

theorem oscillatoryPhasePressure_spec (M : E →L[ℝ] E) (κ : E) {f V : ℝ → E}
    (hf : Continuous f) (hV : Continuous V)
    (hfper : Function.Periodic f 1) (hVper : Function.Periodic V 1)
    (hfmean : phaseMean f = 0) (hVmean : phaseMean V = 0) :
    let p := oscillatoryPhasePressure M κ f V
    phaseMean p = 0 ∧ Function.Periodic p 1 ∧
      ∀ s, HasDerivAt p (oscillatoryPressureSlope M κ (f s) (V s)) s := by
  obtain ⟨hc, hper, hmean⟩ := oscillatory_slope_phase_properties M κ hf hV hfper hVper hfmean hVmean
  exact ⟨phaseMean_phasePrimitive hc, periodic_phasePrimitive hc hper hmean,
    fun s => hasDerivAt_phasePrimitive hc s⟩

theorem norm_oscillatoryPhasePressure_le (M : E →L[ℝ] E) (κ : E) (hκ : κ ≠ 0)
    {f V : ℝ → E} (hf : Continuous f) (hV : Continuous V)
    (hfper : Function.Periodic f 1) (hVper : Function.Periodic V 1)
    (hfmean : phaseMean f = 0) (hVmean : phaseMean V = 0)
    {F W : ℝ} (hF : ∀ s ∈ Icc (0 : ℝ) 1, ‖f s‖ ≤ F)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ‖V s‖ ≤ W) (s : ℝ) :
    ‖oscillatoryPhasePressure M κ f V s‖ ≤ 2 * ((F + 2 * ‖M‖ * W) / ‖κ‖) := by
  obtain ⟨hc, hper, hmean⟩ := oscillatory_slope_phase_properties M κ hf hV hfper hVper hfmean hVmean
  apply norm_phasePrimitive_le hc hper hmean _ s
  intro u hu
  rw [Real.norm_eq_abs]
  exact (abs_oscillatoryPressureSlope_le M κ (f u) (V u) hκ).trans
    (div_le_div_of_nonneg_right (add_le_add (hF u hu)
      (mul_le_mul_of_nonneg_left (hW u hu) (by positivity))) (norm_nonneg κ))

private noncomputable def oscillatoryPhaseMeanCLM : (ℝ →ᵇ E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => phaseMean f
      map_add' := fun f g => phaseMean_add f.continuous g.continuous
      map_smul' := fun c f => phaseMean_const_smul c f } 1
    (fun f => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using
        (norm_phaseMean_le (f := f) fun s _ => f.norm_coe_le_norm s))

private theorem oscillatoryPhaseMean_postcomp (L : E →L[ℝ] E) (f : ℝ →ᵇ E) :
    oscillatoryPhaseMeanCLM (L.compLeftContinuousBounded ℝ f) =
      L (oscillatoryPhaseMeanCLM f) :=
  L.intervalIntegral_comp_comm (f.continuous.intervalIntegrable 0 1)

private noncomputable def oscillatoryPhasePostcomp :
    (E →L[ℝ] E) →L[ℝ] ((ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E)) := by
  let post : (E →L[ℝ] E) →ₗ[ℝ] ((ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E)) :=
    { toFun := fun L => L.compLeftContinuousBounded ℝ
      map_add' := fun L M => by ext f s; simp
      map_smul' := fun c L => by ext f s; simp }
  have hpost (L : E →L[ℝ] E) : ‖post L‖ ≤ 1 * ‖L‖ := by
    change ‖L.compLeftContinuousBounded ℝ‖ ≤ 1 * ‖L‖
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
    refine (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 ?_
    exact fun s => L.le_opNorm_of_le (f.norm_coe_le_norm s)
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E →L[ℝ] E)
    (F := (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E)) (σ := RingHom.id ℝ) post 1 hpost

omit [CompleteSpace E] in
private theorem oscillatoryPhasePostcomp_apply (L : E →L[ℝ] E) (g : ℝ →ᵇ E) (s : ℝ) :
    oscillatoryPhasePostcomp L g s = L (g s) := rfl

/-- At a fixed label, the zero-start solve acts on the entire continuous phase
profile, preserving periodicity and zero mean and furnishing the phase pressure. -/
theorem exists_oscillatoryPhaseSolve_Icc {M : ℝ → E →L[ℝ] E}
    {κ : ℝ → E} {f : ℝ → ℝ →ᵇ E} {l r : ℝ} (hlr : l ≤ r)
    (hM : ContinuousOn M (Icc l r))
    (hκ : ∀ t ∈ Icc l r, HasDerivWithinAt κ (-((M t).adjoint (κ t))) (Icc l r) t)
    (hκ₀ : κ l ≠ 0) (hf : ContinuousOn f (Icc l r))
    (hfper : ∀ t ∈ Icc l r, Function.Periodic (f t : ℝ → E) 1)
    (hfmean : ∀ t ∈ Icc l r, phaseMean (f t : ℝ → E) = 0) :
    ∃ V : ℝ → ℝ →ᵇ E, V l = 0 ∧ ContinuousOn V (Icc l r) ∧ ∀ t ∈ Icc l r,
      Function.Periodic (V t : ℝ → E) 1 ∧ phaseMean (V t : ℝ → E) = 0 ∧
      let p := oscillatoryPhasePressure (M t) (κ t) (f t : ℝ → E) (V t : ℝ → E)
      Function.Periodic p 1 ∧ phaseMean p = 0 ∧ ∀ s,
        ⟪κ t, V t s⟫_ℝ = 0 ∧
        HasDerivAt p (oscillatoryPressureSlope (M t) (κ t) (f t s) (V t s)) s ∧
        HasDerivWithinAt (fun u => V u s) (f t s - M t (V t s) -
          oscillatoryPressureSlope (M t) (κ t) (f t s) (V t s) • κ t) (Icc l r) t := by
  let A (t : ℝ) := affineWaveAmplitudeOperator (M t) (κ t)
  let P (t : ℝ) := oscillatoryTransverseProjection (κ t)
  let post := oscillatoryPhasePostcomp (E := E)
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr⟩
  have hMAdj : ContinuousOn (fun t => -(M t).adjoint) (Icc l r) :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hM).neg
  have hκ_ne : ∀ t ∈ Icc l r, κ t ≠ 0 :=
    linearODE_ne_zero_of_mem ordConnected_Icc hl hMAdj
      (fun t ht => by simpa only [neg_apply] using hκ t ht) hκ₀
  have hκc := HasDerivWithinAt.continuousOn hκ
  have hA : ContinuousOn A (Icc l r) := continuousOn_affineWaveAmplitudeOperator hM hκc hκ_ne
  have hP : ContinuousOn P (Icc l r) := continuousOn_oscillatoryTransverseProjection hκc hκ_ne
  obtain ⟨V, hinit, hV⟩ := linearODE_inhom_exists_Icc hl
    (post.continuous.comp_continuousOn hA)
    ((post.continuous.comp_continuousOn hP).clm_apply hf) 0
  have hpoint (s t : ℝ) (ht : t ∈ Icc l r) : HasDerivWithinAt (fun u => V u s)
      (A t (V t s) + P t (f t s)) (Icc l r) t := by
    simpa only [Function.comp_def, map_add, BoundedContinuousFunction.evalCLM_apply,
      post, oscillatoryPhasePostcomp_apply] using
      (BoundedContinuousFunction.evalCLM ℝ s).hasFDerivAt.comp_hasDerivWithinAt t (hV t ht)
  have hphase (t : ℝ) (ht : t ∈ Icc l r) : Function.Periodic (V t : ℝ → E) 1 := by
    intro s
    let w (u : ℝ) := V u (s + 1) - V u s
    have hw (u : ℝ) (hu : u ∈ Icc l r) : HasDerivWithinAt w (A u (w u)) (Icc l r) u := by
      refine ((hpoint (s + 1) u hu).sub (hpoint s u hu)).congr_deriv ?_
      change A u (V u (s + 1)) + P u (f u (s + 1)) - (A u (V u s) + P u (f u s)) =
        A u (V u (s + 1) - V u s)
      rw [hfper u hu s, map_sub]
      abel
    have heq := linearODE_unique_of_mem (y := fun _ => (0 : E)) ordConnected_Icc hl hA hw
      (fun u _ => by simpa only [map_zero] using hasDerivWithinAt_const u (Icc l r) (0 : E))
      (by simp [w, hinit])
    exact sub_eq_zero.mp (heq ht)
  have hmeanD (t : ℝ) (ht : t ∈ Icc l r) :
      HasDerivWithinAt (fun u => oscillatoryPhaseMeanCLM (V u))
        (A t (oscillatoryPhaseMeanCLM (V t))) (Icc l r) t := by
    refine (oscillatoryPhaseMeanCLM.hasFDerivAt.comp_hasDerivWithinAt t (hV t ht)).congr_deriv ?_
    change oscillatoryPhaseMeanCLM
      ((A t).compLeftContinuousBounded ℝ (V t) + (P t).compLeftContinuousBounded ℝ (f t)) =
      A t (oscillatoryPhaseMeanCLM (V t))
    rw [map_add, oscillatoryPhaseMean_postcomp, oscillatoryPhaseMean_postcomp]
    have hz : oscillatoryPhaseMeanCLM (f t) = 0 := hfmean t ht
    rw [hz, map_zero, add_zero]
  have hmean0 : oscillatoryPhaseMeanCLM (V l) = 0 := by rw [hinit, map_zero]
  have hmean (t : ℝ) (ht : t ∈ Icc l r) : phaseMean (V t : ℝ → E) = 0 :=
    linearODE_unique_of_mem (y := fun _ => (0 : E)) ordConnected_Icc hl hA hmeanD
      (fun u _ => by simpa only [map_zero] using hasDerivWithinAt_const u (Icc l r) (0 : E))
      hmean0 ht
  have hperp (s t : ℝ) (ht : t ∈ Icc l r) : ⟪κ t, V t s⟫_ℝ = 0 :=
    oscillatory_transverse_of_initial ordConnected_Icc hl hκ_ne hκ (hpoint s)
      (by simp [hinit]) t ht
  refine ⟨V, hinit, HasDerivWithinAt.continuousOn hV, fun t ht => ?_⟩
  obtain ⟨hpmean, hpper, hps⟩ := oscillatoryPhasePressure_spec (M t) (κ t)
    (f t).continuous (V t).continuous (hfper t ht) (hphase t ht) (hfmean t ht) (hmean t ht)
  refine ⟨hphase t ht, hmean t ht, hpper, hpmean, fun s => ⟨hperp s t ht, hps s, ?_⟩⟩
  simpa only [A, P, affineWaveAmplitudeOperator_add_transverseProjection] using hpoint s t ht

end TorusEuler
