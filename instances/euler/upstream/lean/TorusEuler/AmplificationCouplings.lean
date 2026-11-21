import TorusEuler.AmplificationAssembly
import TorusEuler.GrowingCouplingComparison
import TorusEuler.GrowingAmplitudePeak

/-! The amplitude and coupling conclusions on a single growing affine path. -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace TorusEuler.GrowingCoupling

open MovingWaveVector (Space)
open NormedSpace (normalize)

private theorem continuousOn_normalize {J : Set ℝ} {v : ℝ → Space}
    (hv : ContinuousOn v J) (hv₀ : ∀ t ∈ J, v t ≠ 0) :
    ContinuousOn (fun t => normalize (v t)) J := by
  unfold NormedSpace.normalize
  exact (hv.norm.inv₀ (fun t ht => norm_ne_zero_iff.2 (hv₀ t ht))).smul hv

private theorem continuousOn_cross3 {J : Set ℝ} {u v : ℝ → Space}
    (hu : ContinuousOn u J) (hv : ContinuousOn v J) :
    ContinuousOn (fun t => cross3 (u t) (v t)) J := by
  unfold cross3
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
    (continuousOn_pi.mpr ?_)
  have hu' (i : Fin 3) : ContinuousOn (fun t => (u t).ofLp i) J :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_continuousOn hu
  have hv' (i : Fin 3) : ContinuousOn (fun t => (v t).ofLp i) J :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_continuousOn hv
  intro i
  fin_cases i
  · exact ((hu' 1).mul (hv' 2)).sub ((hu' 2).mul (hv' 1))
  · exact ((hu' 2).mul (hv' 0)).sub ((hu' 0).mul (hv' 2))
  · exact ((hu' 0).mul (hv' 1)).sub ((hu' 1).mul (hv' 0))

/-- The normalized couplings are continuous on a set where the wave vector
and its amplitude are continuous and nonzero and the strain is continuous. -/
theorem continuousOn_normalized_couplings {J : Set ℝ} {k a : ℝ → Space}
    {M : ℝ → Space →L[ℝ] Space} {S : ℝ}
    (hk : ContinuousOn k J) (ha : ContinuousOn a J) (hM : ContinuousOn M J)
    (hk₀ : ∀ t ∈ J, k t ≠ 0) (ha₀ : ∀ t ∈ J, a t ≠ 0) :
    ContinuousOn (fun t => normalizedNu (M t) (k t) (a t) S) J ∧
      ContinuousOn (fun t => normalizedEta (M t) (k t) (a t) S) J := by
  have hkn := continuousOn_normalize hk hk₀
  have han := continuousOn_normalize ha ha₀
  exact ⟨continuousOn_const.mul (hkn.inner (hM.clm_apply han)),
    continuousOn_const.mul ((continuousOn_cross3 hkn han).inner (hM.clm_apply han))⟩

/-- Nonvanishing of the first normalized coupling gives continuity of the
coupling ratio used to locate the crossing. -/
theorem continuousOn_normalized_coupling_ratio {J : Set ℝ} {k a : ℝ → Space}
    {M : ℝ → Space →L[ℝ] Space} {S : ℝ}
    (hk : ContinuousOn k J) (ha : ContinuousOn a J) (hM : ContinuousOn M J)
    (hk₀ : ∀ t ∈ J, k t ≠ 0) (ha₀ : ∀ t ∈ J, a t ≠ 0)
    (hν : ∀ t ∈ J, normalizedNu (M t) (k t) (a t) S ≠ 0) :
    ContinuousOn (fun t =>
      normalizedEta (M t) (k t) (a t) S / normalizedNu (M t) (k t) (a t) S) J := by
  obtain ⟨hNu, hEta⟩ := continuousOn_normalized_couplings hk ha hM hk₀ ha₀
  exact hEta.div hNu hν

end TorusEuler.GrowingCoupling

namespace TorusEuler.MovingWaveVector.AmplificationWindow

open MovingAmplitude ReferenceAmplitude ReferenceComparison ReferencePropagator
open ReferenceRiccati (rhs s)
open GrowingCoupling (normalizedNu normalizedEta)

noncomputable section

variable {T ε S δ : ℝ} (w : AmplificationWindow T ε S δ)

/-- The new first coupling divided by the older activation coupling. -/
def growingNu (k a : ℝ → Space) (t : ℝ) : ℝ :=
  normalizedNu (w.gradient t) (k t) (a t) S

/-- The new second coupling divided by the older activation coupling. -/
def growingEta (k a : ℝ → Space) (t : ℝ) : ℝ :=
  normalizedEta (w.gradient t) (k t) (a t) S
private theorem coupling_uniform_budget {C T δ ε : ℝ} {p C₀ : ℕ}
    (hT : 2 ≤ T) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hε : ε ≤ 1)
    (hq : p + 9 ≤ C₀) (hC₀ : 2 * (64 * C + 143) ≤ (C₀ : ℝ))
    (hsmall : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε) :
    let κ := (64 * C + 143) * T ^ (p + 9) * δ
    0 ≤ κ ∧ 120 * T ^ 6 * δ ≤ κ ∧ 2 * δ ≤ κ ∧
      64 * C * T ^ (p + 3) * δ + 21 * T ^ 3 * δ ≤ κ ∧ κ ≤ 1 / 2 := by
  let q := p + 9
  let Cκ := 64 * C + 143
  let κ := Cκ * T ^ q * δ
  change 0 ≤ κ ∧ 120 * T ^ 6 * δ ≤ κ ∧ 2 * δ ≤ κ ∧
    64 * C * T ^ (p + 3) * δ + 21 * T ^ 3 * δ ≤ κ ∧ κ ≤ 1 / 2
  have hT₀ : 0 ≤ T := by linarith
  have hT₁ : 1 ≤ T := by linarith
  have hCκ₀ : 0 ≤ Cκ := by unfold Cκ; positivity
  have hκ₀ : 0 ≤ κ := by unfold κ; positivity
  have step {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : m ≤ q) :
      a * T ^ m * δ ≤ a * T ^ q * δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT₁ hm) ha) hδ
  have h₁ := step (show (0 : ℝ) ≤ 120 by norm_num) (m := 6) (by unfold q; omega)
  have h₂ : 2 * δ ≤ 2 * T ^ q * δ := by
    simpa only [pow_zero, mul_one] using step (show (0 : ℝ) ≤ 2 by norm_num) (m := 0)
      (Nat.zero_le q)
  have h₃ := step (show 0 ≤ 64 * C by positivity) (m := p + 3) (by unfold q; omega)
  have h₄ := step (show (0 : ℝ) ≤ 21 by norm_num) (m := 3) (by unfold q; omega)
  have hsum : 120 * T ^ 6 * δ + 2 * δ +
      (64 * C * T ^ (p + 3) * δ + 21 * T ^ 3 * δ) ≤ κ := by
    refine (add_le_add (add_le_add h₁ h₂) (add_le_add h₃ h₄)).trans_eq ?_
    unfold κ Cκ
    ring
  have hκhalf : κ ≤ 1 / 2 := by
    have h : 2 * κ ≤ 1 := calc
      _ = (2 * Cκ) * T ^ q * δ := by unfold κ; ring
      _ ≤ (C₀ : ℝ) * T ^ C₀ * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ
        exact mul_le_mul hC₀ (pow_le_pow_right₀ hT₁ hq) (by positivity) (by positivity)
      _ ≤ ε := hsmall
      _ ≤ _ := hε
    linarith
  exact ⟨hκ₀, by linarith [show 0 ≤ 64 * C * T ^ (p + 3) * δ by positivity,
      show 0 ≤ 21 * T ^ 3 * δ by positivity],
    by linarith [show 0 ≤ 120 * T ^ 6 * δ by positivity,
      show 0 ≤ 64 * C * T ^ (p + 3) * δ by positivity, show 0 ≤ 21 * T ^ 3 * δ by positivity],
    by linarith [show 0 ≤ 120 * T ^ 6 * δ by positivity], hκhalf⟩


/-- A single growing affine wave satisfies (2.9), (2.10), and the positivity
of the first coupling throughout the normalized window of Lemma 2.5. -/
theorem exists_growingWave_log_and_coupling_comparison :
    ∃ N : ℕ, 240 ≤ N ∧ ∀ {T ε S δ scale : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : AmplificationWindow T ε S δ), 0 < scale →
      (C₀ : ℝ) * ε ≤ 1 → (C₀ : ℝ) * T ^ C₀ * δ ≤ ε →
      ∃ k a : ℝ → Space, ∃ Y : ℝ → ℝ,
        k 0 = scale • w.basis 0 2 ∧ a 0 = (-S⁻¹) • w.basis 0 0 + w.basis 0 1 ∧
        Y 0 = 1 ∧ (∀ t ∈ Ici 0, HasDerivWithinAt Y (rhs ε t (Y t)) (Ici 0) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T,
          HasDerivWithinAt a (affineWaveAmplitudeOperator (w.gradient t) (k t) (a t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0 ∧
          |Real.log (‖a t‖ / growingFactor Y t)| ≤ ε) ∧
        (∀ t ∈ Icc 0 T, ε / 2 ≤ w.growingNu k a t) ∧
        (∀ t ∈ Icc 0 T, Real.sqrt 2 / ε ≤ t →
          |w.growingNu k a t - 1| ≤ ε ∧
            |(w.growingEta k a t / w.growingNu k a t) / s ε t - 1| ≤ 1 / 2) := by
  obtain ⟨C, hC, p, hmatrix⟩ := matrixError_polynomial_bound
  let Cκ := 64 * C + 143
  let L := 8 * (256 * Cκ + 2)
  let N := 240 + (p + 19) + Nat.ceil L
  refine ⟨N, by unfold N; omega, ?_⟩
  intro T ε S δ scale C₀ hN w hscale hsmallε hsmallδ
  have hC₀ : L ≤ (C₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil L ≤ C₀ by unfold N at hN; omega))
  have hC₀₁₆ : (16 : ℝ) ≤ (C₀ : ℝ) := by
    exact_mod_cast (show 16 ≤ C₀ by unfold N at hN; omega)
  have hC₀geom : 64 * C + 40 ≤ (C₀ : ℝ) := by
    have h : 64 * C + 40 ≤ L := by unfold L Cκ; linarith only [hC]
    exact h.trans hC₀
  have hC₀coupling : 2 * Cκ ≤ (C₀ : ℝ) := by
    have h : 2 * Cκ ≤ L := by unfold L Cκ; linarith only [hC]
    exact h.trans hC₀
  have hε₁ := w.ratioSmall.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hT₁ : 1 ≤ T := by linarith [w.timeLower]
  have hS₀ : 0 < S := by linarith [w.shearLower]
  have hδ := w.errorNonnegative
  have hAmpBudget := growing_budget_of_polynomial_smallness w.timeLower hC hδ
    (show p + 3 ≤ C₀ by unfold N at hN; omega) (show 4 ≤ C₀ by unfold N at hN; omega)
    hC₀geom hsmallδ
  let κ := Cκ * T ^ (p + 9) * δ
  obtain ⟨hκ, hκwave, hκinv, hκratio, hκhalf⟩ := coupling_uniform_budget (p := p)
    w.timeLower hC hδ hε₁ (show p + 9 ≤ C₀ by unfold N at hN; omega) hC₀coupling hsmallδ
  have hInv : (S ^ 2)⁻¹ ≤ 2 * δ := by
    rw [← inv_pow]
    have hS₁ : S⁻¹ ≤ 1 := (inv_le_one₀ hS₀).mpr w.shearLower
    exact (by nlinarith only [mul_nonneg (inv_nonneg.mpr hS₀.le) (sub_nonneg.mpr hS₁)] :
      S⁻¹ ^ 2 ≤ S⁻¹).trans w.inverseShear
  obtain ⟨k, a, hk0, ha0, hk, ha, hnonzero⟩ := w.exists_growingWave hscale.ne'
  obtain ⟨Y, dev, hYform, hY₀, hY, hdev⟩ :=
    ReferenceRiccati.riccati_exists_Ici w.ratioPositive hε₁
  have hYb (t : ℝ) (ht : t ∈ Icc 0 T) : |Y t| ≤ 1 :=
    ReferenceRiccati.riccati_abs_le_one w.ratioPositive hε₁ hY₀ hY t ht.1
  have hYw (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt Y (rhs ε t (Y t)) (Icc 0 T) t :=
    (hY t ht.1).mono Icc_subset_Ici_self
  have ht0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, by linarith [w.timeLower]⟩
  obtain ⟨hU₀, hV₀⟩ := growing_components (w.orthonormal_basis ht0) hS₀.ne' ha0
  have hsys (t : ℝ) (ht : t ∈ Icc 0 T) :=
    w.raw_amplitude_equations hscale.ne' hk0 hk ha ht (hnonzero t ht).2.2
  let d := 32 * C * T ^ (p + 3) * δ
  have hd : d ≤ 1 / 2 := by
    unfold d
    nlinarith only [hAmpBudget, hε₁, show 0 ≤ 40 * T ^ 4 * δ by positivity]
  have hstate (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖normalizedState ε Y (U w.basis a S) (V w.basis a) t - (1, 0)‖ ≤ d := by
    let η := C * T ^ p * δ
    let D := ∫ r in 0..t, ((1 + |Y r|) ^ 2 / s ε r) * η
    obtain ⟨hD₀, hDraw⟩ := integrated_growing_error_le w.ratioPositive.le hε₁ w.timeLower
      ht (show 0 ≤ η by unfold η; positivity) (HasDerivWithinAt.continuousOn hYw) hYb
    have hD₁ : D ≤ 4 * C * T ^ (p + 3) * δ := by
      convert hDraw using 1
      rw [pow_add]
      unfold η
      ring
    change 0 ≤ D at hD₀
    have hDle : D ≤ 1 / 4 :=
      by nlinarith only [hD₁, hAmpBudget, hε₁, show 0 ≤ 40 * T ^ 4 * δ by positivity]
    have hExp : Real.exp (2 * D) ≤ 2 := by
      have h := Real.abs_exp_sub_one_le (x := 2 * D)
        (by rw [abs_of_nonneg (by positivity)]; linarith)
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * D)] at h
      linarith [(abs_le.mp h).2]
    have hclose := normalized_close_to_growing_of_raw_matrix w.ratioPositive hY₀ hU₀ hV₀ hYw
      (w.continuousOn_matrixError hscale.ne' hk0 hk) (hη := continuousOn_const)
      (hmatrix w hscale.ne' hk0 hk) (fun r hr => (hsys r hr).1) (fun r hr => (hsys r hr).2) ht
    change ‖normalizedState ε Y (U w.basis a S) (V w.basis a) t - (1, 0)‖ ≤
      4 * Real.exp (2 * D) * D at hclose
    calc
      _ ≤ 4 * Real.exp (2 * D) * D := hclose
      _ ≤ 8 * D := by nlinarith only [mul_nonneg hD₀ (sub_nonneg.mpr hExp)]
      _ ≤ d := by unfold d; nlinarith only [hD₁]
  have hlog (t : ℝ) (ht : t ∈ Icc 0 T) :
      |Real.log (‖a t‖ / growingFactor Y t)| ≤ ε := by
    obtain ⟨hZ, _, hX, hQ, _⟩ := w.wave_geometry hscale.ne' hk0 hk ht
    calc
      _ ≤ 2 * d + 20 * T ^ 4 * (S ^ 2)⁻¹ :=
        log_growing_physical_norm_le (w.orthonormal_basis ht) hscale.ne' hS₀
          (hnonzero t ht).2.2 hT₁ hX hQ hZ (hYb t ht) hd (hstate t ht)
      _ ≤ 2 * d + 20 * T ^ 4 * (2 * δ) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hInv (by positivity))
      _ = 64 * C * T ^ (p + 3) * δ + 40 * T ^ 4 * δ := by unfold d; ring
      _ ≤ ε := hAmpBudget
  have hTδ : T * δ ≤ 1 := by
    have hpow : T ≤ T ^ 6 := by
      simpa only [pow_one] using pow_le_pow_right₀ hT₁ (show 1 ≤ (6 : ℕ) by decide)
    nlinarith only [w.smallness, mul_le_mul_of_nonneg_right hpow hδ]
  have hStrength := strengthRatio_bound hTδ w.trace_zero w.preceding_data w.preceding_vector
    (fun t ht => by simpa only [affineWaveAmplitudeOperator_apply] using w.preceding_amplitude t ht)
    w.older_bound
  have herrors (t : ℝ) (ht : t ∈ Icc 0 T) :
      |w.growingNu k a t - ReferenceRiccati.referenceNu ε t Y| ≤ 256 * T ^ 8 * κ + 2 * δ ∧
      |w.growingEta k a t - ReferenceRiccati.referenceEta ε t Y| ≤ 256 * T ^ 8 * κ + 2 * δ := by
    obtain ⟨hV, hUratio⟩ := raw_ratio_close_of_growing_state_close hd (hstate t ht)
    have hwaves := (w.wave_comparison hscale.ne' hk0 hk ht).1
    have hwaves' := hwaves.trans ((le_of_eq (by ring : 120 * δ * T ^ 6 = 120 * T ^ 6 * δ)).trans hκwave)
    have hX : |X w.basis k scale t - ReferenceRiccati.x ε t| ≤ κ :=
      by linarith only [hwaves', abs_nonneg (Q w.basis k scale S t + ε * t),
        abs_nonneg (Z w.basis k scale t - 1)]
    have hQ : |Q w.basis k scale S t + ε * t| ≤ κ :=
      by linarith only [hwaves', abs_nonneg (X w.basis k scale t - ReferenceRiccati.x ε t),
        abs_nonneg (Z w.basis k scale t - 1)]
    have hZ : |Z w.basis k scale t - 1| ≤ κ :=
      by linarith only [hwaves', abs_nonneg (X w.basis k scale t - ReferenceRiccati.x ε t),
        abs_nonneg (Q w.basis k scale S t + ε * t)]
    have hw : |U w.basis a S t / V w.basis a t - Y t| + 21 * T ^ 3 * δ ≤ κ := by
      refine (add_le_add hUratio le_rfl).trans ?_
      simpa only [d, ← mul_assoc, show (2 : ℝ) * 32 = 64 by norm_num] using hκratio
    exact GrowingCoupling.normalized_couplings_sub_reference_le (w.B t) (w.E t)
      w.timeLower ht w.ratioPositive.le hε₁ (hYb t ht) (w.orthonormal_basis ht) rfl
      hscale w.shearLower hV (hnonzero t ht).2.2 hδ hκ hκhalf hX hQ hZ
      (hInv.trans hκinv) hw (w.older_bound t ht) (w.first_coupling t ht) (w.third_coupling t ht)
      (hStrength t ht) (w.error_bound t ht)
  obtain ⟨hν, hCoupling⟩ := GrowingCoupling.coupling_conclusions_of_polynomial_budget
    (C := Cκ) (p := p + 9) w.ratioPositive w.timeLower hδ hC₀₁₆
    (show (p + 9) + 10 ≤ C₀ by unfold N at hN; omega) hC₀ hsmallε hsmallδ hYform hdev
    (show κ ≤ Cκ * T ^ (p + 9) * δ from le_rfl) herrors
  exact ⟨k, a, Y, hk0, ha0, hY₀, hY, hk, ha,
    fun t ht => ⟨(hnonzero t ht).1, (hnonzero t ht).2.1, (hnonzero t ht).2.2, hlog t ht⟩,
    hν, hCoupling⟩

open AmplificationCrossing (crossingHorizon)

/-- The same growing wave provides a crossing and the peak-normalized
strength and early-gain estimates in Proposition 2.6. -/
theorem exists_growingWave_crossing :
    ∃ N : ℕ, 240 ≤ N ∧ ∀ {T ε S δ scale next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : AmplificationWindow T ε S δ), 0 < scale →
      (C₀ : ℝ) * ε ≤ 1 → (C₀ : ℝ) * T ^ C₀ * δ ≤ ε →
      0 < next → next ≤ ε / 32 → crossingHorizon ε next ≤ T →
      ∃ k a : ℝ → Space, ∃ Y : ℝ → ℝ,
        k 0 = scale • w.basis 0 2 ∧ a 0 = (-S⁻¹) • w.basis 0 0 + w.basis 0 1 ∧
        Y 0 = 1 ∧ (∀ t ∈ Ici 0, HasDerivWithinAt Y (rhs ε t (Y t)) (Ici 0) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T,
          HasDerivWithinAt a (affineWaveAmplitudeOperator (w.gradient t) (k t) (a t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0 ∧
          |Real.log (‖a t‖ / growingFactor Y t)| ≤ ε) ∧
        (∀ t ∈ Icc 0 T, ε / 2 ≤ w.growingNu k a t) ∧
        (∀ t ∈ Icc 0 T, Real.sqrt 2 / ε ≤ t →
          |w.growingNu k a t - 1| ≤ ε ∧
            |(w.growingEta k a t / w.growingNu k a t) / s ε t - 1| ≤ 1 / 2) ∧
        ∃ τm ∈ Icc (2 / ε) (3 / ε), Y τm = 0 ∧
          ∃ peak : ℝ, IsGreatest ((fun r => ‖a r‖) '' Icc 0 T) peak ∧
            (Real.exp (-ε) * growingFactor Y τm ≤ peak ∧
              peak ≤ Real.exp ε * growingFactor Y τm) ∧
            (∃ τ ∈ Ioo τm (crossingHorizon ε next), w.growingEta k a τ / w.growingNu k a τ = next) ∧
            (∀ τ ∈ Icc τm (crossingHorizon ε next),
              w.growingEta k a τ / w.growingNu k a τ = next →
                (Real.exp (-1) / 4) * (Real.sqrt (ε * next))⁻¹ ≤
                  ‖a τ‖ * ‖k τ‖ / (scale * peak) ∧
                ‖a τ‖ * ‖k τ‖ / (scale * peak) ≤
                  18 * Real.exp 3 * (Real.sqrt (ε * next))⁻¹) ∧
            (∀ τ ∈ Icc 0 1, ‖a τ‖ ≤ Real.exp (3 - (Real.sqrt ε)⁻¹) * peak) := by
  obtain ⟨N, hN, hcompare⟩ := exists_growingWave_log_and_coupling_comparison
  refine ⟨N, hN, ?_⟩
  intro T ε S δ scale next C₀ hC₀ w hscale hsmallε hsmallδ hnext hnextsmall hT
  obtain ⟨k, a, Y, hk₀, ha₀, hY₀, hY, hk, ha, hpath, hν, hcoupling⟩ :=
    hcompare hC₀ w hscale hsmallε hsmallδ
  let ρ (t : ℝ) := w.growingEta k a t / w.growingNu k a t
  have hK (t : ℝ) (ht : t ∈ Icc 0 T) : k t ≠ 0 := (hpath t ht).1
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : a t ≠ 0 := (hpath t ht).2.1
  have hLog (t : ℝ) (ht : t ∈ Icc 0 T) : |Real.log (‖a t‖ / growingFactor Y t)| ≤ ε :=
    (hpath t ht).2.2.2
  have haContinuous := HasDerivWithinAt.continuousOn ha
  have hρ : ContinuousOn ρ (Icc 0 T) :=
    GrowingCoupling.continuousOn_normalized_coupling_ratio (HasDerivWithinAt.continuousOn hk)
      haContinuous w.continuousOn_gradient hK hA
      (fun t ht => ((half_pos w.ratioPositive).trans_le (hν t ht)).ne')
  have hcomp (t : ℝ) (ht : t ∈ Icc (Real.sqrt 2 / ε) T) :
      s ε t / 2 ≤ ρ t ∧ ρ t ≤ 3 / 2 * s ε t := by
    have hterr : t ∈ Icc 0 T :=
      ⟨(div_nonneg (Real.sqrt_nonneg _) w.ratioPositive.le).trans ht.1, ht.2⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hcoupling t hterr ht.1).2
    have hl : 1 / 2 ≤ ρ t / s ε t := by unfold ρ; linarith only [hlo]
    have hh : ρ t / s ε t ≤ 3 / 2 := by unfold ρ; linarith only [hhi]
    exact ⟨((le_div_iff₀ (ReferenceRiccati.s_pos ε t)).mp hl).trans_eq' (by ring),
      (div_le_iff₀ (ReferenceRiccati.s_pos ε t)).mp hh⟩
  have hsubset : Icc (2 / ε) T ⊆ Icc 0 T :=
    Icc_subset_Icc_left (div_nonneg (by norm_num) w.ratioPositive.le)
  have hGeom (t : ℝ) (ht : t ∈ Icc (2 / ε) T) :
      |X w.basis k scale t - ReferenceRiccati.x ε t| ≤ 1 / 2 ∧
        |Q w.basis k scale S t + ε * t| ≤ 1 / 2 ∧
        |Z w.basis k scale t - 1| ≤ 1 / 2 := by
    obtain ⟨h, hb⟩ := w.wave_comparison hscale.ne' hk₀ hk (hsubset ht)
    exact ⟨by linarith only [h, hb, abs_nonneg (Q w.basis k scale S t + ε * t),
              abs_nonneg (Z w.basis k scale t - 1)],
      by linarith only [h, hb, abs_nonneg (X w.basis k scale t - ReferenceRiccati.x ε t),
        abs_nonneg (Z w.basis k scale t - 1)],
      by linarith only [h, hb, abs_nonneg (X w.basis k scale t - ReferenceRiccati.x ε t),
        abs_nonneg (Q w.basis k scale S t + ε * t)]⟩
  have hεsmall : 2 * ε ≤ 1 := by linarith only [w.ratioSmall]
  have hcross := growing_amplitude_crossing_strength_and_gain w.ratioPositive hεsmall
    hnext hnextsmall hT hscale w.shearLower hY₀ hY haContinuous hA hLog
    (fun _ ht => w.orthonormal_basis (hsubset ht)) (fun t ht => (hGeom t ht).1)
    (fun t ht => (hGeom t ht).2.1) (fun t ht => (hGeom t ht).2.2) hρ hcomp
  exact ⟨k, a, Y, hk₀, ha₀, hY₀, hY, hk, ha, hpath, hν, hcoupling, hcross⟩


end

end TorusEuler.MovingWaveVector.AmplificationWindow
