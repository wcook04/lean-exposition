import TorusEuler.AffineExistence
import TorusEuler.AmplitudePolynomialBounds
import TorusEuler.GrowingAmplitudeBudget
import TorusEuler.GrowingAmplitudePropagator

/-! Assembly of the wave-vector and amplitude estimates of Lemmas 2.3 and 2.5
on the same normalized affine-wave path. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.MovingWaveVector

open MovingAmplitude ReferenceAmplitude

noncomputable section

/-- The preceding wave and the pointwise estimates on the normalized strains
on the slab of Lemma 2.3. -/
structure AmplificationWindow (T ε S δ : ℝ) where
  kp : ℝ → Space
  ap : ℝ → Space
  B : ℝ → Space →L[ℝ] Space
  E : ℝ → Space →L[ℝ] Space
  timeLower : 2 ≤ T
  ratioPositive : 0 < ε
  ratioSmall : ε ≤ 1 / 2
  shearLower : 1 ≤ S
  inverseShear : S⁻¹ ≤ 2 * δ
  errorNonnegative : 0 ≤ δ
  smallness : 240 * δ * T ^ 6 ≤ 1
  older_continuous : ContinuousOn B (Icc 0 T)
  error_continuous : ContinuousOn E (Icc 0 T)
  trace_zero : ∀ t ∈ Icc 0 T, LinearMap.trace ℝ Space (B t).toLinearMap = 0
  preceding_data : ∀ t ∈ Icc 0 T, kp t ≠ 0 ∧ ap t ≠ 0 ∧ ⟪kp t, ap t⟫_ℝ = 0
  preceding_vector : ∀ t ∈ Icc 0 T,
    HasDerivWithinAt kp (-((B t).adjoint (kp t))) (Icc 0 T) t
  preceding_amplitude : ∀ t ∈ Icc 0 T, HasDerivWithinAt ap
    (affineWaveAmplitudeOperator (B t) (kp t) (ap t)) (Icc 0 T) t
  older_bound : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ δ
  error_bound : ∀ t ∈ Icc 0 T, ‖E t‖ ≤ δ / S
  first_coupling : ∀ t ∈ Icc 0 T, |2 * S * entry (frame kp ap t) (B t) 0 1 - 1| ≤ δ
  third_coupling : ∀ t ∈ Icc 0 T, |2 * S * entry (frame kp ap t) (B t) 2 1 - ε| ≤ δ

namespace AmplificationWindow

variable {T ε S δ scale : ℝ} (w : AmplificationWindow T ε S δ)

abbrev basis : ℝ → Fin 3 → Space := frame w.kp w.ap

abbrev shearRatio : ℝ → ℝ := strengthRatio w.kp w.ap

def gradient (t : ℝ) : Space →L[ℝ] Space := strain (w.basis t) (w.B t) (w.E t) S (w.shearRatio t)

def matrixError (k : ℝ → Space) (scale t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  errorOperator ε t (entry (w.basis t) (w.B t)) (entry (w.basis t) (w.gradient t))
    (X w.basis k scale t) (Q w.basis k scale S t) (Z w.basis k scale t) S

theorem orthonormal_basis {t : ℝ} (ht : t ∈ Icc 0 T) : Orthonormal ℝ (w.basis t) := by
  obtain ⟨hk, ha, hp⟩ := w.preceding_data t ht
  exact orthonormal_movingFrame hk ha hp

theorem continuousOn_basis (i : Fin 3) : ContinuousOn (fun t => w.basis t i) (Icc 0 T) := by
  intro t ht
  obtain ⟨hk, ha, hp⟩ := w.preceding_data t ht
  have h := hasDerivWithinAt_movingFrame ht (w.B t) (w.trace_zero t ht)
    hk ha hp (w.preceding_vector t ht)
    (by simpa only [affineWaveAmplitudeOperator_apply] using w.preceding_amplitude t ht)
  fin_cases i
  · exact h.1.continuousWithinAt
  · exact h.2.1.continuousWithinAt
  · exact h.2.2.1.continuousWithinAt

theorem continuousOn_gradient : ContinuousOn w.gradient (Icc 0 T) := by
  have hkp := HasDerivWithinAt.continuousOn w.preceding_vector
  have hap := HasDerivWithinAt.continuousOn w.preceding_amplitude
  have hs : ContinuousOn w.shearRatio (Icc 0 T) :=
    (hkp.norm.mul hap.norm).div_const _
  have hrank : ContinuousOn (fun t => InnerProductSpace.rankOne ℝ (w.basis t 1) (w.basis t 0))
      (Icc 0 T) :=
    ((InnerProductSpace.rankOne ℝ).continuous.comp_continuousOn
      (w.continuousOn_basis 1)).clm_apply (w.continuousOn_basis 0)
  have hShear := (hs.const_mul S).smul hrank
  exact (w.older_continuous.add hShear).add w.error_continuous

/-- The normalized affine wave exists with the transverse growing seed of (2.9). -/
theorem exists_growingWave (hscale : scale ≠ 0) :
    ∃ k a : ℝ → Space,
      k 0 = scale • w.basis 0 2 ∧ a 0 = (-S⁻¹) • w.basis 0 0 + w.basis 0 1 ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T,
        HasDerivWithinAt a (affineWaveAmplitudeOperator (w.gradient t) (k t) (a t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0 := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, by linarith [w.timeLower]⟩
  have he := w.orthonormal_basis h0
  have hinner := orthonormal_iff_ite.mp he
  have hk : w.basis 0 2 ≠ 0 := by
    have h := he.norm_eq_one 2
    intro hzero
    rw [hzero, norm_zero] at h
    norm_num at h
  have ha : (-S⁻¹) • w.basis 0 0 + w.basis 0 1 ≠ 0 := by
    have h : ⟪w.basis 0 1, (-S⁻¹) • w.basis 0 0 + w.basis 0 1⟫_ℝ = 1 := by
      simp [inner_add_right, real_inner_smul_right, hinner, he.norm_eq_one]
    intro hzero
    rw [hzero, inner_zero_right] at h
    norm_num at h
  have hperp : ⟪scale • w.basis 0 2, (-S⁻¹) • w.basis 0 0 + w.basis 0 1⟫_ℝ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, inner_add_right, hinner]
  obtain ⟨k, a, hk0, ha0, hk', ha', hprop⟩ :=
    affineWave_exists_Icc h0 w.continuousOn_gradient (smul_ne_zero hscale hk) ha hperp
  exact ⟨k, a, hk0, ha0, hk', fun t ht => by
    simpa only [affineWaveAmplitudeOperator_apply] using ha' t ht, hprop⟩

private theorem rate_error_small (w : AmplificationWindow T ε S δ) : T * δ ≤ 1 := by
  have hT : 1 ≤ T := by linarith [w.timeLower]
  have hpow : T ≤ T ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hT (show 1 ≤ (6 : ℕ) by decide)
  nlinarith only [w.smallness, mul_le_mul_of_nonneg_right hpow w.errorNonnegative]

theorem wave_comparison {k : ℝ → Space} (hscale : scale ≠ 0)
    (hk0 : k 0 = scale • w.basis 0 2)
    (hk : ∀ t ∈ Icc 0 T, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    |X w.basis k scale t - ReferenceRiccati.x ε t| +
      |Q w.basis k scale S t + ε * t| + |Z w.basis k scale t - 1| ≤ 120 * δ * T ^ 6 ∧
      120 * δ * T ^ 6 ≤ 1 / 2 :=
  moving_waveVector_polynomial_error w.ratioPositive.le (w.ratioSmall.trans (by norm_num))
    w.timeLower w.errorNonnegative hscale w.shearLower w.smallness w.trace_zero w.preceding_data
    w.preceding_vector (fun t ht => by
      simpa only [affineWaveAmplitudeOperator_apply] using w.preceding_amplitude t ht)
    hk hk0 w.older_bound w.error_bound w.third_coupling t ht

theorem wave_geometry {k : ℝ → Space} (hscale : scale ≠ 0)
    (hk0 : k 0 = scale • w.basis 0 2)
    (hk : ∀ t ∈ Icc 0 T, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    1 / 2 ≤ Z w.basis k scale t ∧ Z w.basis k scale t ≤ 3 / 2 ∧
      |X w.basis k scale t| ≤ T ^ 2 ∧ |Q w.basis k scale S t| ≤ T ∧
      1 / 4 ≤ normFactor (X w.basis k scale t) (Q w.basis k scale S t) (Z w.basis k scale t) S := by
  obtain ⟨hclose, hsmall⟩ := w.wave_comparison hscale hk0 hk ht
  exact waveVector_coordinate_bounds w.ratioPositive.le w.ratioSmall w.timeLower ht (hclose.trans hsmall)

theorem continuousOn_matrixError {k : ℝ → Space} (hscale : scale ≠ 0)
    (hk0 : k 0 = scale • w.basis 0 2)
    (hk : ∀ t ∈ Icc 0 T, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t) :
    ContinuousOn (w.matrixError k scale) (Icc 0 T) := by
  have hkC := HasDerivWithinAt.continuousOn hk
  have hinner (i : Fin 3) : ContinuousOn (fun t => ⟪w.basis t i, k t⟫_ℝ) (Icc 0 T) :=
    (w.continuousOn_basis i).inner hkC
  exact continuousOn_errorOperator (by linarith [w.shearLower])
    (fun t ht => (show 0 < Z w.basis k scale t by linarith [(w.wave_geometry hscale hk0 hk ht).1]).ne')
    (fun i j => (w.continuousOn_basis i).inner (w.older_continuous.clm_apply (w.continuousOn_basis j)))
    (fun i j => (w.continuousOn_basis i).inner (w.continuousOn_gradient.clm_apply (w.continuousOn_basis j)))
    ((hinner 0).div_const _) (((hinner 1).const_mul S).div_const _) ((hinner 2).div_const _)

/-- The bounds in Lemma 2.3 come from one matrix path, shared by all amplitudes. -/
theorem matrixError_polynomial_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ {T ε S δ scale : ℝ}
      (w : AmplificationWindow T ε S δ) {k : ℝ → Space}, scale ≠ 0 →
      k 0 = scale • w.basis 0 2 →
      (∀ t ∈ Icc 0 T,
        HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t) →
      ∀ t ∈ Icc 0 T, ‖w.matrixError k scale t‖ ≤ C * T ^ p * δ := by
  obtain ⟨C, hC, p, hbound⟩ := errorOperator_le_on_normalized_window
  refine ⟨C, hC, p, ?_⟩
  intro T ε S δ scale w k hscale hk0 hk t ht
  have hstrength := strengthRatio_bound w.rate_error_small w.trace_zero w.preceding_data
    w.preceding_vector (fun t ht => by
      simpa only [affineWaveAmplitudeOperator_apply] using w.preceding_amplitude t ht) w.older_bound t ht
  obtain ⟨hclose, hsmall⟩ := w.wave_comparison hscale hk0 hk ht
  exact hbound (w.orthonormal_basis ht) (w.B t) (w.E t) w.timeLower ht.1 ht.2
    w.ratioPositive.le (w.ratioSmall.trans (by norm_num)) w.shearLower w.inverseShear
    w.errorNonnegative hsmall hclose (w.older_bound t ht) (w.error_bound t ht)
    (w.first_coupling t ht) (w.third_coupling t ht) hstrength

theorem raw_amplitude_equations {k a : ℝ → Space} (hscale : scale ≠ 0)
    (hk0 : k 0 = scale • w.basis 0 2)
    (hk : ∀ t ∈ Icc 0 T, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t)
    (ha : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt a (affineWaveAmplitudeOperator (w.gradient t) (k t) (a t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) (hperp : ⟪k t, a t⟫_ℝ = 0) :
    let u := U w.basis a S
    let v := V w.basis a
    let R := w.matrixError k scale t
    HasDerivWithinAt u (-ReferenceRiccati.damping ε t * u t +
      ReferenceRiccati.driving ε t * v t + (R (u t, v t)).1) (Icc 0 T) t ∧
    HasDerivWithinAt v (u t + (R (u t, v t)).2) (Icc 0 T) t := by
  obtain ⟨hpK, hpA, hp⟩ := w.preceding_data t ht
  have hZ : Z w.basis k scale t ≠ 0 := (show 0 < Z w.basis k scale t by
    linarith [(w.wave_geometry hscale hk0 hk ht).1]).ne'
  exact moving_amplitude_perturbed ht hscale (by linarith [w.shearLower])
    (w.trace_zero t ht) hpK hpA hp (w.preceding_vector t ht)
    (by simpa only [affineWaveAmplitudeOperator_apply] using w.preceding_amplitude t ht)
    hZ hperp (by simpa only [affineWaveAmplitudeOperator_apply, gradient] using ha t ht)

/-- For any sufficiently large absolute threshold, the same affine wave constructed
with the growing seed obeys (2.9) on the entire normalized slab. -/
theorem exists_growingWave_log_comparison :
    ∃ N : ℕ, 240 ≤ N ∧ ∀ {T ε S δ scale : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : AmplificationWindow T ε S δ), scale ≠ 0 → (C₀ : ℝ) * T ^ C₀ * δ ≤ ε →
      ∃ k a : ℝ → Space, ∃ Y : ℝ → ℝ,
        k 0 = scale • w.basis 0 2 ∧ a 0 = (-S⁻¹) • w.basis 0 0 + w.basis 0 1 ∧
        Y 0 = 1 ∧
        (∀ t ∈ Ici 0, HasDerivWithinAt Y (ReferenceRiccati.rhs ε t (Y t)) (Ici 0) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T,
          HasDerivWithinAt a (affineWaveAmplitudeOperator (w.gradient t) (k t) (a t)) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0 ∧
          |Real.log (‖a t‖ / ReferencePropagator.growingFactor Y t)| ≤ ε := by
  obtain ⟨C, hC, p, hbound⟩ := matrixError_polynomial_bound
  let N := 240 + (p + 3) + Nat.ceil (64 * C + 40)
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro T ε S δ scale C₀ hN w hscale hsmall
  have hN' : 64 * C + 40 ≤ (C₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (64 * C + 40) ≤ C₀ by dsimp [N] at hN; omega))
  have hbudget := growing_budget_of_polynomial_smallness w.timeLower hC w.errorNonnegative
    (show p + 3 ≤ C₀ by dsimp [N] at hN; omega) (by dsimp [N] at hN; omega) hN' hsmall
  obtain ⟨k, a, hk0, ha0, hk, ha, hnonzero⟩ := w.exists_growingWave hscale
  have hε₁ := w.ratioSmall.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  obtain ⟨Y, _, _, hY₀, hY, _⟩ := ReferenceRiccati.riccati_exists_Ici w.ratioPositive hε₁
  have hYb := ReferenceRiccati.riccati_abs_le_one w.ratioPositive hε₁ hY₀ hY
  have ht0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, by linarith [w.timeLower]⟩
  obtain ⟨hU₀, hV₀⟩ := growing_components (w.orthonormal_basis ht0) (by linarith [w.shearLower]) ha0
  have hsys (t : ℝ) (ht : t ∈ Icc 0 T) :=
    w.raw_amplitude_equations hscale hk0 hk ha ht (hnonzero t ht).2.2
  refine ⟨k, a, Y, hk0, ha0, hY₀, hY, hk, ha, fun t ht => ?_⟩
  obtain ⟨hkt, hat, hperp⟩ := hnonzero t ht
  obtain ⟨hZ, _, hX, hQ, _⟩ := w.wave_geometry hscale hk0 hk ht
  exact ⟨hkt, hat, hperp, log_growing_physical_norm_of_raw_matrix
    w.ratioPositive hε₁ w.timeLower hC w.errorNonnegative hbudget w.shearLower w.inverseShear
    hscale hY₀ (fun r hr => hYb r hr.1) (fun r hr => (hY r hr.1).mono Icc_subset_Ici_self)
    (w.continuousOn_matrixError hscale hk0 hk) (hbound w hscale hk0 hk)
    hU₀ hV₀ (fun r hr => (hsys r hr).1) (fun r hr => (hsys r hr).2)
    ht (w.orthonormal_basis ht) hperp hX hQ hZ⟩

end AmplificationWindow

end

end TorusEuler.MovingWaveVector
