import TorusEuler.ExactAffineEuler
import TorusEuler.PhysicalGrowthPropagator

/-! The six named statements of the frozen paper in the affine and
amplification subsections. Derivatives at the time-slab endpoints are taken
within the slab. The finite-window results use the paper's normalized clock
and the exact four-term physical error. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.PaperAffine

open MovingWaveVector ReferenceRiccati
open ReferencePropagator (growingFactor)
open AmplificationCrossing (crossingHorizon)

noncomputable section

/-- The two equations of (2.1) on a prescribed interval. -/
def WaveOn (J : Set ℝ) (D : ℝ → Vec3 →L[ℝ] Vec3) (k a : ℝ → Vec3) : Prop :=
  (∀ t ∈ J, HasDerivWithinAt k (-((D t).adjoint (k t))) J t) ∧
  (∀ t ∈ J, HasDerivWithinAt a (affineWaveAmplitudeOperator (D t) (k t) (a t)) J t)

/-- Lemma 2.1, `cc:lem:wave`. The Euler equations and preservation
of nonzero transverse data hold for the same affine-wave solution. -/
theorem exactWave {J : Set ℝ} (hJ : J.OrdConnected) (hDiff : UniqueDiffOn ℝ J)
    {F P : ℝ → ℝ} (hF : Differentiable ℝ F) (hP : ∀ z, HasDerivAt P (F z) z)
    {D D' : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
    (hD : ∀ t ∈ J, HasDerivWithinAt D (D' t) J t)
    (hS : ∀ t ∈ J, IsSelfAdjoint (D' t + (D t).comp (D t)))
    (htr : ∀ t ∈ J, LinearMap.trace ℝ Vec3 (D t).toLinearMap = 0)
    (hWave : WaveOn J D k a) :
    (∀ ⦃t₀ : ℝ⦄, t₀ ∈ J → k t₀ ≠ 0 → a t₀ ≠ 0 → ⟪k t₀, a t₀⟫_ℝ = 0 →
      ∀ t ∈ J, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0) ∧
    ((∀ t ∈ J, ⟪k t, a t⟫_ℝ = 0) → ∀ t ∈ J, ∀ x,
      derivWithin (fun r => affineWaveVelocity F D k a r x) J t +
        fderiv ℝ (affineWaveVelocity F D k a t) x (affineWaveVelocity F D k a t x) +
        gradient (affineWavePressure P (D' t + (D t).comp (D t))
          (affineWavePressureCoeff (D t) (k t) (a t)) (k t)) x = 0 ∧
      divergence (affineWaveVelocity F D k a t) x = 0) := by
  have ha (t : ℝ) (ht : t ∈ J) : HasDerivWithinAt a
      (-(D t (a t)) + affineWavePressureCoeff (D t) (k t) (a t) • k t) J t := by
    simpa only [affineWaveAmplitudeOperator_apply, affineWavePressureCoeff] using hWave.2 t ht
  exact ⟨fun _ ht₀ => affineWave_propagation hJ ht₀ (HasDerivWithinAt.continuousOn hD)
    hWave.1 ha, affineWave_solvesEulerOn hDiff hF hP hD hS htr hWave.1 ha⟩

/-- Lemma 2.2, `cc:lem:frame`. The normalized moving frame, its
three derivatives, and the logarithmic-strength derivative. -/
theorem movingFrameDerivatives {J : Set ℝ} {B : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
    (htr : ∀ t ∈ J, LinearMap.trace ℝ Vec3 (B t).toLinearMap = 0)
    (hWave : WaveOn J B k a)
    (hData : ∀ t ∈ J, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0) :
    let e := frame k a
    ∀ t ∈ J, Orthonormal ℝ (e t) ∧
      HasDerivWithinAt (fun u => e u 0)
        (-(entry (e t) (B t) 0 1) • e t 1 - entry (e t) (B t) 0 2 • e t 2) J t ∧
      HasDerivWithinAt (fun u => e u 1)
        (entry (e t) (B t) 0 1 • e t 0 - entry (e t) (B t) 2 1 • e t 2) J t ∧
      HasDerivWithinAt (fun u => e u 2)
        (entry (e t) (B t) 0 2 • e t 0 + entry (e t) (B t) 2 1 • e t 1) J t ∧
      HasDerivWithinAt (fun u => Real.log (‖k u‖ * ‖a u‖)) (entry (e t) (B t) 2 2) J t := by
  intro e t ht
  obtain ⟨hk, ha, hp⟩ := hData t ht
  refine ⟨orthonormal_movingFrame hk ha hp, ?_⟩
  simpa only [e, frame, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using
    hasDerivWithinAt_movingFrame ht (B t) (htr t ht) hk ha hp (hWave.1 t ht)
      (by simpa only [affineWaveAmplitudeOperator_apply] using hWave.2 t ht)

/-- Lemma 2.4, `cc:lem:model`. The global Riccati reference solution
has the stated deviation, sign, and gain, with a unique turning time. -/
theorem referenceModel {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ (Y e : ℝ → ℝ) (τm : ℝ), Y = referenceY ε e ∧ Y 0 = 1 ∧
      (∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) ∧
      MapsTo e (Ici 0) (Icc 0 (ε / 8)) ∧ (∀ τ ∈ Ici 0, |Y τ| ≤ 1) ∧
      2 ≤ ε * τm ∧ ε * τm ≤ 3 ∧
      (∀ τ ∈ Ici 0, Y τ = 0 ↔ τ = τm) ∧
      (∀ τ ∈ Ico 0 τm, 0 < Y τ) ∧ (∀ τ ∈ Ioi τm, Y τ < 0) ∧
      (Real.sqrt ε)⁻¹ - 1 ≤ ∫ τ in 0..τm, Y τ := by
  obtain ⟨Y, e, m, hform, hY₀, hY, he, habs, hm, hz, hpos, hneg, hGain⟩ :=
    riccati_reference_solution hε hε₁
  refine ⟨Y, e, m, hform, hY₀, hY, he, habs, by
    simpa only [mul_comm ε] using (div_le_iff₀ hε).mp hm.1, by
    simpa only [mul_comm ε] using (le_div_iff₀ hε).mp hm.2, ?_, hpos, hneg, hGain⟩
  intro τ hτ
  constructor
  · intro hZero
    rcases lt_trichotomy τ m with ht | ht | ht
    · exact ((hpos τ ⟨hτ, ht⟩).ne' hZero).elim
    · exact ht
    · exact ((hneg τ ht).ne hZero).elim
  · rintro rfl
    exact hz

private theorem norm_three_le (u v z : ℝ) :
    ‖(WithLp.toLp 2 ![u, v, z] : Vec3)‖ ≤ |u| + |v| + |z| := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  change u ^ 2 + v ^ 2 + z ^ 2 ≤ _
  nlinarith only [sq_abs u, sq_abs v, sq_abs z, mul_nonneg (abs_nonneg u) (abs_nonneg v),
    mul_nonneg (abs_nonneg u) (abs_nonneg z), mul_nonneg (abs_nonneg v) (abs_nonneg z)]

/-- Lemma 2.3, `cc:uf:exact:lem:additive`. For the exact physical
window and clock, one continuous error operator works for every transverse
amplitude. The sum of the three coordinate errors bounds their Euclidean
norm. -/
theorem additiveComparison :
    ∃ (N p : ℕ) (C : ℝ), 240 ≤ N ∧ 0 ≤ C ∧
      ∀ {I : Set ℝ} {t₀ T scale : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : PhysicalAmplification I t₀) (k : ℝ → Vec3), 2 ≤ T → 0 < scale →
      MapsTo w.clock (Icc 0 T) I →
      (C₀ : ℝ) * w.ratio ≤ 1 → (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
      k t₀ = scale • w.basis t₀ 2 →
      (∀ t ∈ I, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) I t) →
      let K := k ∘ w.clock
      let e : ℝ → Fin 3 → Space := fun t => w.basis (w.clock t)
      let S := w.shear
      let δ := w.errorSize
      let ε := w.ratio
      C * T ^ p * δ ≤ 1 / 2 ∧
      sSup ((fun τ => ‖(WithLp.toLp 2 ![X e K scale τ - x ε τ,
        Q e K scale S τ + ε * τ, Z e K scale τ - 1] : Vec3)‖) '' Icc 0 T) ≤ C * T ^ p * δ ∧
      (∀ τ ∈ Icc 0 T, |X e K scale τ - x ε τ| + |Q e K scale S τ + ε * τ| +
        |Z e K scale τ - 1| ≤ C * T ^ p * δ) ∧
      ∃ R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), ContinuousOn R (Icc 0 T) ∧
        sSup ((fun τ => ‖R τ‖) '' Icc 0 T) ≤ C * T ^ p * δ ∧
        (∀ τ ∈ Icc 0 T, ‖R τ‖ ≤ C * T ^ p * δ) ∧
        ∀ a : ℝ → Vec3,
          WaveOn I w.gradient k a → (∀ t ∈ I, ⟪k t, a t⟫_ℝ = 0) →
          let u := MovingAmplitude.U e (a ∘ w.clock) S
          let v := MovingAmplitude.V e (a ∘ w.clock)
          ∀ τ ∈ Icc 0 T, HasDerivWithinAt u
            (-damping ε τ * u τ + driving ε τ * v τ + (R τ (u τ, v τ)).1) (Icc 0 T) τ ∧
            HasDerivWithinAt v (u τ + (R τ (u τ, v τ)).2) (Icc 0 T) τ := by
  obtain ⟨L, hL, d, hMatrix⟩ := AmplificationWindow.matrixError_polynomial_bound
  let C := max 120 L
  let p := max 6 d
  let N := max 240 (max p (Nat.ceil C))
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 120).trans (le_max_left _ _)
  refine ⟨N, p, C, le_max_left _ _, hC, ?_⟩
  intro I t₀ T scale C₀ hNC w k hT hscale hclock hsmallε hsmallδ hk₀ hk K e S δ ε
  have hC₀ : 240 ≤ C₀ := (le_max_left _ _).trans hNC
  let W := w.toNormalized hT hC₀ hclock hsmallε hsmallδ
  have hK₀ : K 0 = scale • W.basis 0 2 := by
    simpa only [K, W, Function.comp_apply, PhysicalAmplification.clock_zero,
      PhysicalAmplification.toNormalized, AmplificationWindow.basis, PhysicalAmplification.basis, frame]
      using hk₀
  have hK := (w.rescale_wave hT hC₀ hclock hsmallε hsmallδ hk
    (a := fun _ => 0) (by
      intro t ht
      simpa only [map_zero] using hasDerivWithinAt_const t I (0 : Vec3))).1
  have hT₁ : 1 ≤ T := by linarith
  have hp : p ≤ C₀ := (le_max_left _ _).trans ((le_max_right _ _).trans hNC)
  have hCupper : C ≤ (C₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil C ≤ C₀ from
      (le_max_right _ _).trans ((le_max_right _ _).trans hNC)))
  have hEnlarge {A : ℝ} {j : ℕ} (hA : A ≤ C) (hj : j ≤ p) :
      A * T ^ j * δ ≤ C * T ^ p * δ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul hA (pow_le_pow_right₀ hT₁ hj) (by positivity) hC) W.errorNonnegative
  have hClose (τ : ℝ) (hτ : τ ∈ Icc 0 T) :
      |X e K scale τ - x ε τ| + |Q e K scale S τ + ε * τ| + |Z e K scale τ - 1| ≤ C * T ^ p * δ := by
    exact (W.wave_comparison hscale.ne' hK₀ hK hτ).1.trans
      ((le_of_eq (by ring : 120 * δ * T ^ 6 = 120 * T ^ 6 * δ)).trans
        (hEnlarge (le_max_left _ _) (le_max_left _ _)))
  have hError (τ : ℝ) (hτ : τ ∈ Icc 0 T) : ‖W.matrixError K scale τ‖ ≤ C * T ^ p * δ :=
    (hMatrix W hscale.ne' hK₀ hK τ hτ).trans (hEnlarge (le_max_right _ _) (le_max_right _ _))
  have hNonempty : (Icc (0 : ℝ) T).Nonempty := ⟨0, le_rfl, by linarith⟩
  refine ⟨?_, ?_, hClose, W.matrixError K scale, W.continuousOn_matrixError hscale.ne' hK₀ hK,
    ?_, hError, ?_⟩
  · exact (amplification_absorb_power hT₁ W.errorNonnegative hC hp hCupper hsmallδ).trans W.ratioSmall
  · apply csSup_le (hNonempty.image _)
    rintro _ ⟨τ, hτ, rfl⟩
    exact (norm_three_le _ _ _).trans (hClose τ hτ)
  · apply csSup_le (hNonempty.image _)
    rintro _ ⟨τ, hτ, rfl⟩
    exact hError τ hτ
  · intro a hWave hperp u v τ hτ
    have hA := (w.rescale_wave hT hC₀ hclock hsmallε hsmallδ hk hWave.2).2
    exact W.raw_amplitude_equations hscale.ne' hK₀ hK hA hτ (hperp _ (hclock hτ))

private theorem eqOn_wave {J : Set ℝ} (hJ : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    {D : ℝ → Vec3 →L[ℝ] Vec3} (hD : ContinuousOn D J)
    {k a k' a' : ℝ → Vec3} (hWave : WaveOn J D k a) (hWave' : WaveOn J D k' a')
    (hk₀ : k t₀ = k' t₀) (ha₀ : a t₀ = a' t₀) (hkn : ∀ t ∈ J, k' t ≠ 0) :
    EqOn k k' J ∧ EqOn a a' J := by
  have hAdj : ContinuousOn (fun t => -(D t).adjoint) J :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hD).neg
  have hk : EqOn k k' J :=
    linearODE_unique_of_mem hJ ht₀ hAdj
      (fun t ht => by simpa only [neg_apply] using hWave.1 t ht)
      (fun t ht => by simpa only [neg_apply] using hWave'.1 t ht) hk₀
  have hAmp := continuousOn_affineWaveAmplitudeOperator hD
    (HasDerivWithinAt.continuousOn hWave'.1) hkn
  exact ⟨hk, linearODE_unique_of_mem hJ ht₀ hAmp
    (fun t ht => by simpa only [← hk ht] using hWave.2 t ht)
    hWave'.2 ha₀⟩

private theorem factor_eqOn {Y Z : ℝ → ℝ} (h : EqOn Y Z (Ici 0)) :
    EqOn (growingFactor Y) (growingFactor Z) (Ici 0) := by
  intro t ht
  unfold growingFactor
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le ht] at hx
  exact h hx.1

private theorem normalizedComparison :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {T ε S δ scale : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (W : AmplificationWindow T ε S δ) {K A : ℝ → Vec3} {Y : ℝ → ℝ}, 0 < scale →
      (C₀ : ℝ) * ε ≤ 1 → (C₀ : ℝ) * T ^ C₀ * δ ≤ ε →
      K 0 = scale • W.basis 0 2 → A 0 = (-S⁻¹) • W.basis 0 0 + W.basis 0 1 →
      WaveOn (Icc 0 T) W.gradient K A →
      Y 0 = 1 → (∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) →
      (∀ τ ∈ Icc 0 T, K τ ≠ 0 ∧ A τ ≠ 0 ∧ ⟪K τ, A τ⟫_ℝ = 0 ∧
        |Real.log (‖A τ‖ / growingFactor Y τ)| ≤ ε) ∧
      (∀ τ ∈ Icc 0 T, ε / 2 ≤ W.growingNu K A τ) ∧
      (∀ τ ∈ Icc 0 T, Real.sqrt 2 / ε ≤ τ →
        |W.growingNu K A τ - 1| ≤ ε ∧
        |(W.growingEta K A τ / W.growingNu K A τ) / s ε τ - 1| ≤ 1 / 2) := by
  obtain ⟨N, hN, hCompare⟩ := AmplificationWindow.exists_growingWave_log_and_coupling_comparison
  refine ⟨N, hN, ?_⟩
  intro T ε S δ scale C₀ hNC W K A Y hscale hsmallε hsmallδ hK₀ hA₀ hWave hY₀ hY
  obtain ⟨k, a, Y', hk₀, ha₀, hY'₀, hY', hk, ha, hPath, hNu, hLate⟩ :=
    hCompare hNC W hscale hsmallε hsmallδ
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, by linarith [W.timeLower]⟩
  obtain ⟨hK, hA⟩ := eqOn_wave ordConnected_Icc h0 W.continuousOn_gradient hWave ⟨hk, ha⟩
    (hK₀.trans hk₀.symm) (hA₀.trans ha₀.symm) (fun τ hτ => (hPath τ hτ).1)
  have he : ε ≤ 1 := W.ratioSmall.trans (by norm_num)
  have hFactor := factor_eqOn (riccati_unique_Ici W.ratioPositive he hY₀ hY'₀ hY hY')
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    rw [hK hτ, hA hτ, hFactor hτ.1]
    exact hPath τ hτ
  · intro τ hτ
    simpa only [AmplificationWindow.growingNu, hK hτ, hA hτ] using hNu τ hτ
  · intro τ hτ hLateTime
    simpa only [AmplificationWindow.growingNu, AmplificationWindow.growingEta, hK hτ, hA hτ]
      using hLate τ hτ hLateTime

/-- A fixed comparison threshold for the prescribed normalized wave. -/
theorem finiteWindowNormalizedComparison :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {T ε S δ scale : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (W : AmplificationWindow T ε S δ) {K A : ℝ → Vec3} {Y : ℝ → ℝ}, 0 < scale →
      (C₀ : ℝ) * ε ≤ 1 → (C₀ : ℝ) * T ^ C₀ * δ ≤ ε →
      K 0 = scale • W.basis 0 2 → A 0 = (-S⁻¹) • W.basis 0 0 + W.basis 0 1 →
      WaveOn (Icc 0 T) W.gradient K A →
      Y 0 = 1 → (∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) →
      (∀ τ ∈ Icc 0 T, K τ ≠ 0 ∧ A τ ≠ 0 ∧ ⟪K τ, A τ⟫_ℝ = 0 ∧
        |Real.log (‖A τ‖ / growingFactor Y τ)| ≤ ε) ∧
      (∀ τ ∈ Icc 0 T, ε / 2 ≤ W.growingNu K A τ) ∧
      (∀ τ ∈ Icc 0 T, Real.sqrt 2 / ε ≤ τ →
        |W.growingNu K A τ - 1| ≤ ε ∧
        |(W.growingEta K A τ / W.growingNu K A τ) / s ε τ - 1| ≤ 1 / 2) ∧
      (∀ ⦃u v : ℝ⦄, u ∈ Icc 0 T → v ∈ Icc u T →
        ∃ Φ : transversePlane (K u) ≃L[ℝ] transversePlane (K v),
          ‖Φ.toContinuousLinearMap‖ ≤ 252 * Real.exp 1 * S * (‖A v‖ / ‖A u‖) ∧
          ∀ (b : ℝ → Vec3),
            WaveOn (Icc 0 T) W.gradient K b →
            ∀ (hB : ∀ t ∈ Icc 0 T, ⟪K t, b t⟫_ℝ = 0),
              ∀ hu : u ∈ Icc 0 T, (Φ ⟨b u, mem_transversePlane.mpr (hB u hu)⟩ : Vec3) = b v) := by
  obtain ⟨Ncmp, hNcmp, hCompare⟩ := normalizedComparison
  obtain ⟨Ngrow, _, hGrow⟩ := AmplificationWindow.exists_growth_bound_threshold
  refine ⟨max Ncmp Ngrow, hNcmp.trans (le_max_left _ _), ?_⟩
  intro T ε S δ scale C₀ hNC W K A Y hscale hε hδ hK₀ hA₀ hWave hY₀ hY
  obtain ⟨hPath, hNu, hLate⟩ := hCompare ((le_max_left _ _).trans hNC) W hscale hε hδ
    hK₀ hA₀ hWave hY₀ hY
  refine ⟨hPath, hNu, hLate, ?_⟩
  intro u v hu hv
  have hv' : v ∈ Icc 0 T := ⟨hu.1.trans hv.1, hv.2⟩
  have hKn t ht := (hPath t ht).1
  obtain ⟨Φ, hΦ⟩ := exists_affineWave_transverse_equiv_Icc hu hv' W.continuousOn_gradient hKn hWave.1
  have hAmp t ht : A t ≠ 0 ∧ ⟪K t, A t⟫_ℝ = 0 :=
    ⟨(hPath t ht).2.1, (hPath t ht).2.2.1⟩
  refine ⟨Φ, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by have := W.shearLower; positivity)
    intro b₀
    obtain ⟨b, hb₀, hb₁, hb, hperp⟩ := hΦ b₀
    change ‖(Φ b₀ : Vec3)‖ ≤ _ * ‖(b₀ : Vec3)‖
    rw [← hb₀, ← hb₁]
    have hAv : 0 < ‖A v‖ := norm_pos_iff.mpr (hAmp v hv').1
    have h := (div_le_iff₀ hAv).mp
      (hGrow ((le_max_right _ _).trans hNC) W hscale.ne' (c := 1) one_pos hδ
        hK₀ (by simpa only [one_smul] using hA₀) hWave.1 hWave.2 hb hAmp hperp hY₀ hY hu hv)
    exact h.trans_eq (by ring)
  · intro b hB hPerp hu'
    let b₀ : transversePlane (K u) := ⟨b u, mem_transversePlane.mpr (hPerp u hu')⟩
    obtain ⟨c, hc₀, hc₁, hc, _⟩ := hΦ b₀
    have hAcontinuous := continuousOn_affineWaveAmplitudeOperator W.continuousOn_gradient
      (HasDerivWithinAt.continuousOn hWave.1) hKn
    have hcb := linearODE_unique_of_mem ordConnected_Icc hu hAcontinuous hc hB.2 hc₀
    exact hc₁.symm.trans (hcb hv')

private theorem normalized_inputs {I : Set ℝ} {t₀ T scale : ℝ} {C₀ : ℕ}
    (w : PhysicalAmplification I t₀) (hT : 2 ≤ T) (hC₀ : 240 ≤ C₀)
    (hclock : MapsTo w.clock (Icc 0 T) I)
    (hε : (C₀ : ℝ) * w.ratio ≤ 1) (hδ : (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio)
    {k a : ℝ → Vec3} (hk₀ : k t₀ = scale • w.basis t₀ 2)
    (ha₀ : a t₀ = (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1)
    (hWave : WaveOn I w.gradient k a) :
    let W := w.toNormalized hT hC₀ hclock hε hδ
    let K := k ∘ w.clock
    let A := a ∘ w.clock
    K 0 = scale • W.basis 0 2 ∧ A 0 = (-w.shear⁻¹) • W.basis 0 0 + W.basis 0 1 ∧
      WaveOn (Icc 0 T) W.gradient K A := by
  intro W K A
  have hb : W.basis 0 = w.basis t₀ := by
    funext i
    simp only [W, PhysicalAmplification.toNormalized, AmplificationWindow.basis, frame,
      PhysicalAmplification.clock_zero]
  exact ⟨by simpa only [K, Function.comp_apply, PhysicalAmplification.clock_zero, hb] using hk₀,
    by simpa only [A, Function.comp_apply, PhysicalAmplification.clock_zero, hb] using ha₀,
    w.rescale_wave hT hC₀ hclock hε hδ hWave.1 hWave.2⟩

/-- Lemma 2.5, `cc:lem:finite-comparison`. The comparison and all
transverse propagators refer to the prescribed growing wave, with a single
threshold independent of the physical time window. -/
theorem finiteComparison :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {I : Set ℝ} {t₀ T scale : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : PhysicalAmplification I t₀) {k a : ℝ → Vec3} {Y : ℝ → ℝ},
      2 ≤ T → 0 < scale → ∀ hclock : MapsTo w.clock (Icc 0 T) I,
      (C₀ : ℝ) * w.ratio ≤ 1 → (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
      k t₀ = scale • w.basis t₀ 2 →
      a t₀ = (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1 →
      WaveOn I w.gradient k a → Y 0 = 1 →
      (∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs w.ratio τ (Y τ)) (Ici 0) τ) →
      let K := k ∘ w.clock
      let A := a ∘ w.clock
      (∀ τ ∈ Icc 0 T,
        |Real.log (‖A τ‖ / growingFactor Y τ)| ≤ w.ratio ∧
        w.ratio * w.firstCoupling / 2 ≤ w.physicalNu k a (w.clock τ)) ∧
      (∀ τ ∈ Icc 0 T, Real.sqrt 2 / w.ratio ≤ τ →
        |w.physicalNu k a (w.clock τ) / w.firstCoupling - 1| ≤ w.ratio ∧
        |(w.physicalEta k a (w.clock τ) / w.physicalNu k a (w.clock τ)) / s w.ratio τ - 1| ≤ 1 / 2) ∧
      (∀ ⦃u v : ℝ⦄, u ∈ Icc 0 T → v ∈ Icc u T →
        ∃ Φ : transversePlane (K u) ≃L[ℝ] transversePlane (K v),
          ‖Φ.toContinuousLinearMap‖ ≤ 252 * Real.exp 1 * w.shear * (‖A v‖ / ‖A u‖) ∧
          ∀ b : ℝ → Vec3, WaveOn I w.gradient k b →
            ∀ (hB : ∀ t ∈ I, ⟪k t, b t⟫_ℝ = 0), ∀ hu : u ∈ Icc 0 T,
              (Φ ⟨b (w.clock u), mem_transversePlane.mpr (hB _ (hclock hu))⟩ : Vec3) = b (w.clock v)) := by
  obtain ⟨N, hN, hCompare⟩ := finiteWindowNormalizedComparison
  refine ⟨N, hN, ?_⟩
  intro I t₀ T scale C₀ hNC w k a Y hT hscale hclock hε hδ hk₀ ha₀ hWave hY₀ hY K A
  let W := w.toNormalized hT (hN.trans hNC) hclock hε hδ
  obtain ⟨hK₀, hA₀, hWaveNorm⟩ := normalized_inputs w hT (hN.trans hNC) hclock hε hδ hk₀ ha₀ hWave
  obtain ⟨hPath, hNu, hLate, hProp⟩ := hCompare hNC W hscale hε hδ hK₀ hA₀ hWaveNorm hY₀ hY
  have hCoupling (τ : ℝ) (hτ : τ ∈ Icc 0 T) :
      W.growingNu K A τ = w.physicalNu k a (w.clock τ) / w.firstCoupling ∧
      W.growingEta K A τ = w.physicalEta k a (w.clock τ) / w.firstCoupling :=
    w.toNormalized_couplings_eq hT (hN.trans hNC) hclock hε hδ hτ (K τ) (A τ)
  have hFirst : 0 < w.firstCoupling := w.first_coupling_positive
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    have hNu' := hNu τ hτ
    rw [(hCoupling τ hτ).1] at hNu'
    exact ⟨(hPath τ hτ).2.2.2,
      (by simpa only [div_mul_eq_mul_div, mul_comm w.firstCoupling w.ratio] using
        (le_div_iff₀ hFirst).mp hNu')⟩
  · intro τ hτ hLag
    have h := hLate τ hτ hLag
    rw [(hCoupling τ hτ).1, (hCoupling τ hτ).2,
      div_div_div_cancel_right₀ hFirst.ne'] at h
    exact h
  · intro u v hu hv
    obtain ⟨Φ, hΦ, hAll⟩ := hProp hu hv
    refine ⟨Φ, hΦ, ?_⟩
    intro b hB hPerp hu'
    have hBn : WaveOn (Icc 0 T) W.gradient K (b ∘ w.clock) :=
      w.rescale_wave hT (hN.trans hNC) hclock hε hδ hB.1 hB.2
    exact hAll (b ∘ w.clock) hBn (fun t ht => hPerp _ (hclock ht)) hu'

/-- Proposition 2.6, `cc:prop:finite-return`. The crossing, strength
bounds, and early gain refer to the prescribed wave and its actual maximum
on the full normalized slab. -/
theorem finiteReturn :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {I : Set ℝ} {t₀ T scale next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : PhysicalAmplification I t₀) {k a : ℝ → Vec3} {Y : ℝ → ℝ},
      2 ≤ T → 0 < scale → MapsTo w.clock (Icc 0 T) I →
      (C₀ : ℝ) * w.ratio ≤ 1 → (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
      k t₀ = scale • w.basis t₀ 2 →
      a t₀ = (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1 →
      WaveOn I w.gradient k a → Y 0 = 1 →
      (∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs w.ratio τ (Y τ)) (Ici 0) τ) →
      0 < next → next ≤ w.ratio / 32 → crossingHorizon w.ratio next ≤ T →
      let ε := w.ratio
      let H := crossingHorizon ε next
      let ρ := fun τ => w.physicalEta k a (w.clock τ) / w.physicalNu k a (w.clock τ)
      ∃ τm ∈ Icc (2 / ε) (3 / ε), Y τm = 0 ∧
        ∃ peak : ℝ, IsGreatest ((fun τ => ‖a (w.clock τ)‖) '' Icc 0 T) peak ∧
          (∃ τ ∈ Ioo τm H, ρ τ = next) ∧
          (∀ τ ∈ Icc τm H, ρ τ = next →
            (18 * Real.exp 3)⁻¹ * (Real.sqrt (ε * next))⁻¹ ≤
              ‖a (w.clock τ)‖ * ‖k (w.clock τ)‖ / (scale * peak) ∧
            ‖a (w.clock τ)‖ * ‖k (w.clock τ)‖ / (scale * peak) ≤
              18 * Real.exp 3 * (Real.sqrt (ε * next))⁻¹) ∧
          (∀ τ ∈ Icc 0 1, ‖a (w.clock τ)‖ ≤ Real.exp (3 - (Real.sqrt ε)⁻¹) * peak) := by
  obtain ⟨N, hN, hCross⟩ := AmplificationWindow.exists_growingWave_crossing
  refine ⟨N, hN, ?_⟩
  intro I t₀ T scale next C₀ hNC w k a Y hT hscale hclock hε hδ hk₀ ha₀ hWave
    hY₀ hY hnext hnext' hH ε H ρ
  let W := w.toNormalized hT (hN.trans hNC) hclock hε hδ
  let K := k ∘ w.clock
  let A := a ∘ w.clock
  obtain ⟨hK₀, hA₀, hWaveNorm⟩ := normalized_inputs w hT (hN.trans hNC) hclock hε hδ hk₀ ha₀ hWave
  obtain ⟨k', a', Y', hk'₀, ha'₀, hY'₀, hY', hk', ha', hPath, _, _,
    τm, hm, hYm, peak, hPeak, _, hCrossing, hStrength, hGain⟩ :=
    hCross hNC W hscale hε hδ hnext hnext' hH
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, by linarith⟩
  obtain ⟨hK, hA⟩ := eqOn_wave ordConnected_Icc h0 W.continuousOn_gradient hWaveNorm ⟨hk', ha'⟩
    (hK₀.trans hk'₀.symm) (hA₀.trans ha'₀.symm) (fun τ hτ => (hPath τ hτ).1)
  have hKe {τ : ℝ} (hτ : τ ∈ Icc 0 T) : K τ = k' τ := hK hτ
  have hAe {τ : ℝ} (hτ : τ ∈ Icc 0 T) : A τ = a' τ := hA hτ
  have hτm₀ : 0 ≤ τm := (div_nonneg (by norm_num) w.ratio_pos.le).trans hm.1
  have hSub : Icc τm H ⊆ Icc 0 T := Icc_subset_Icc hτm₀ hH
  have hYeq := riccati_unique_Ici w.ratio_pos (W.ratioSmall.trans (by norm_num)) hY₀ hY'₀ hY hY'
  have hFirst : w.firstCoupling ≠ 0 := w.first_coupling_positive.ne'
  have hRatio (τ : ℝ) (hτ : τ ∈ Icc 0 T) :
      W.growingEta k' a' τ / W.growingNu k' a' τ = ρ τ := by
    have hCoupling :
        W.growingNu K A τ = w.physicalNu k a (w.clock τ) / w.firstCoupling ∧
        W.growingEta K A τ = w.physicalEta k a (w.clock τ) / w.firstCoupling :=
      w.toNormalized_couplings_eq hT (hN.trans hNC) hclock hε hδ hτ (K τ) (A τ)
    simp only [AmplificationWindow.growingNu, AmplificationWindow.growingEta] at hCoupling ⊢
    rw [← hKe hτ, ← hAe hτ, hCoupling.1, hCoupling.2, div_div_div_cancel_right₀ hFirst]
  have hImage : ((fun τ => ‖a (w.clock τ)‖) '' Icc 0 T) = ((fun τ => ‖a' τ‖) '' Icc 0 T) :=
    EqOn.image_eq (fun _ hτ => congrArg norm (hAe hτ))
  have hCoeff : (18 * Real.exp 3)⁻¹ ≤ Real.exp (-1) / 4 := by
    have hExp : Real.exp 1 ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
    have hComp : 4 * Real.exp 1 ≤ 18 * Real.exp 3 := by
      linarith only [mul_le_mul_of_nonneg_left hExp (by norm_num : (0 : ℝ) ≤ 4), Real.exp_pos 3]
    rw [Real.exp_neg, inv_div_left]
    exact inv_anti₀ (by positivity : 0 < 4 * Real.exp 1) hComp
  refine ⟨τm, hm, (hYeq hτm₀).trans hYm, peak, hImage.symm ▸ hPeak, ?_, ?_, ?_⟩
  · obtain ⟨τ, hτ, hR⟩ := hCrossing
    exact ⟨τ, hτ, (hRatio τ (hSub (Ioo_subset_Icc_self hτ))).symm.trans hR⟩
  · intro τ hτ hρ
    have hτ' := hSub hτ
    have h := hStrength τ hτ ((hRatio τ hτ').trans hρ)
    change _ ≤ ‖A τ‖ * ‖K τ‖ / _ ∧ ‖A τ‖ * ‖K τ‖ / _ ≤ _
    rw [hAe hτ', hKe hτ']
    exact ⟨(mul_le_mul_of_nonneg_right hCoeff (by positivity)).trans h.1, h.2⟩
  · intro τ hτ
    have hτ' : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans (by linarith)⟩
    change ‖A τ‖ ≤ _
    rw [hAe hτ']
    exact hGain τ hτ

end

end TorusEuler.PaperAffine
