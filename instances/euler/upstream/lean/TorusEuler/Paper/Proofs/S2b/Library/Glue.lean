import TorusEuler.Paper.S2.Statements
import TorusEuler.GrowingCouplingComparison
import TorusEuler.GrowingAmplitudePeak

/-! # Glue for the proofs of Lemmas 2.4, 2.6, 2.7 and Proposition 2.8

Routine facts shared by the conditional proofs of package S2b (namespace
`TorusEuler.Paper.Lib.S2b`). None of them carries the content of a numbered result:

* the angle `φ` of (2.4) in the library's variables (`cos φ = s`, `tan φ = x`,
  `ετ sin 2φ = damping`, `cos²φ(1 - ε tan φ) = driving`) and the Riccati problem (2.12)
  in the library form;
* continuity of the frame of the preceding wave, proved from the continuity of `k_p` and
  `a_p` alone (the library proof `PhysicalAmplification.continuousOn_basis` uses the frame
  equations of Lemma 2.2, which the proofs of 2.6-2.8 do not cite);
* the normalized coefficient bounds that follow from the definition (2.6) of `δ` and the
  bounds (2.8) on `S` (`sections/03_amplification.tex:201-263`);
* the dictionary between the scaled components `ζ`, `α` of (2.3) and the library
  coordinates `X, Q, Z` and `U = -α₁`, `V = α₂`, and the conjugation by
  `P = diag(-1, 1)` that turns the system of Lemma 2.4 into the library's raw system.
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S2b

open MovingWaveVector MovingAmplitude ReferenceRiccati

noncomputable section

/-! ## The angle `φ` of (2.4) -/

/-- `cos φ = (1 + x²)^{-1/2}`, the library's `s`. -/
theorem cos_referenceAngle (ε τ : ℝ) : Real.cos (referenceAngle ε τ) = s ε τ := by
  rw [referenceAngle, Real.cos_arctan, s, x, one_div]

/-- `tan φ = x = ετ²/2`. -/
theorem tan_referenceAngle_eq_x (ε τ : ℝ) : Real.tan (referenceAngle ε τ) = x ε τ :=
  Real.tan_arctan _

/-- `sin φ = x s`. -/
theorem sin_referenceAngle (ε τ : ℝ) : Real.sin (referenceAngle ε τ) = x ε τ * s ε τ := by
  rw [referenceAngle, Real.sin_arctan, s, x, div_eq_mul_inv]

/-- `ετ sin 2φ` is the library's damping coefficient. -/
theorem damping_eq (ε τ : ℝ) : ε * τ * Real.sin (2 * referenceAngle ε τ) = damping ε τ := by
  rw [Real.sin_two_mul, sin_referenceAngle, cos_referenceAngle, damping]; ring

/-- `cos²φ(1 - ε tan φ)` is the library's driving coefficient. -/
theorem driving_eq (ε τ : ℝ) :
    Real.cos (referenceAngle ε τ) ^ 2 * (1 - ε * Real.tan (referenceAngle ε τ)) =
      driving ε τ := by
  rw [cos_referenceAngle, tan_referenceAngle_eq_x, driving]

/-- The Riccati problem (2.12) in the library form. -/
theorem referenceSlope_iff {ε : ℝ} {Y : ℝ → ℝ} : ReferenceSlope ε Y ↔
    (Y 0 = 1 ∧ ∀ τ ∈ Ici (0 : ℝ), HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) := by
  simp only [ReferenceSlope, driving_eq, damping_eq, rhs]

/-- The reference matrix of (2.5) is the conjugate of the library's `referenceMatrix`
by `P = diag(-1, 1)`, entrywise. -/
theorem referenceSystemMatrix_apply (ε τ : ℝ) :
    referenceSystemMatrix ε τ 0 0 = -damping ε τ ∧
      referenceSystemMatrix ε τ 0 1 = -driving ε τ ∧
      referenceSystemMatrix ε τ 1 0 = -1 ∧ referenceSystemMatrix ε τ 1 1 = 0 := by
  simp only [referenceSystemMatrix, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    damping_eq, driving_eq, neg_zero, and_self]

/-- The form (2.13) of a solution of (2.12) in the library variables: if
`Y = (1 + e)cos φ - ετ sin 2φ/4` at `τ`, then the library deviation of `Y` is `e`. -/
theorem deviation_eq_of_form {ε τ : ℝ} {Y e : ℝ → ℝ}
    (h : Y τ = (1 + e τ) * Real.cos (referenceAngle ε τ) -
      ε * τ * Real.sin (2 * referenceAngle ε τ) / 4) :
    deviation ε Y τ = e τ := by
  rw [cos_referenceAngle, damping_eq] at h
  unfold deviation
  rw [h]
  field_simp [(s_pos ε τ).ne']
  ring

/-! ## Continuity of the frame -/

/-- Normalization is continuous away from zero. -/
theorem continuousOn_normalize {J : Set ℝ} {v : ℝ → Space}
    (hv : ContinuousOn v J) (hv₀ : ∀ t ∈ J, v t ≠ 0) :
    ContinuousOn (fun t => NormedSpace.normalize (v t)) J := by
  unfold NormedSpace.normalize
  exact (hv.norm.inv₀ (fun t ht => norm_ne_zero_iff.2 (hv₀ t ht))).smul hv

/-- The cross product is continuous. -/
theorem continuousOn_cross3 {J : Set ℝ} {u v : ℝ → Space}
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

/-- The frame `(k_p/|k_p|, a_p/|a_p|, k_p/|k_p| × a_p/|a_p|)` is continuous where `k_p`
and `a_p` are continuous and nonzero. -/
theorem continuousOn_frame {J : Set ℝ} {kp ap : ℝ → Space}
    (hk : ContinuousOn kp J) (ha : ContinuousOn ap J)
    (hk₀ : ∀ t ∈ J, kp t ≠ 0) (ha₀ : ∀ t ∈ J, ap t ≠ 0) (i : Fin 3) :
    ContinuousOn (fun t => frame kp ap t i) J := by
  have h0 := continuousOn_normalize hk hk₀
  have h1 := continuousOn_normalize ha ha₀
  fin_cases i
  · exact h0
  · exact h1
  · exact continuousOn_cross3 h0 h1

variable {I : Set ℝ} {t₀ : ℝ}

/-- The frame of the preceding wave is continuous on the window. -/
theorem basis_continuousOn (w : PhysicalAmplification I t₀) (i : Fin 3) :
    ContinuousOn (fun t => w.basis t i) I :=
  continuousOn_frame (HasDerivWithinAt.continuousOn w.preceding_vector)
    (HasDerivWithinAt.continuousOn w.preceding_amplitude)
    (fun t ht => (w.preceding_data t ht).1) (fun t ht => (w.preceding_data t ht).2.1) i

/-- The frame of the preceding wave is orthonormal on the window. -/
theorem basis_orthonormal (w : PhysicalAmplification I t₀) {t : ℝ} (ht : t ∈ I) :
    Orthonormal ℝ (w.basis t) :=
  orthonormal_movingFrame (w.preceding_data t ht).1 (w.preceding_data t ht).2.1
    (w.preceding_data t ht).2.2

/-- The full gradient `M = B + a_p ⊗ k_p + E_c` is continuous on the window. -/
theorem gradient_continuousOn (w : PhysicalAmplification I t₀) :
    ContinuousOn w.gradient I := by
  have hkp := HasDerivWithinAt.continuousOn w.preceding_vector
  have hap := HasDerivWithinAt.continuousOn w.preceding_amplitude
  have hrank : ContinuousOn (fun t => InnerProductSpace.rankOne ℝ (w.ap t) (w.kp t)) I :=
    ((InnerProductSpace.rankOne ℝ).continuous.comp_continuousOn hap).clm_apply hkp
  exact (w.older_continuous.add hrank).add w.error_continuous

/-- The clock `t₀ + τ/r` is continuous. -/
theorem clock_continuous (w : PhysicalAmplification I t₀) : Continuous w.clock :=
  continuous_const.add (continuous_id.div_const _)

/-- A function continuous on the window is continuous in `τ` on `[0, T]`. -/
theorem continuousOn_comp_clock {E : Type*} [TopologicalSpace E]
    (w : PhysicalAmplification I t₀) {T : ℝ} (hclock : MapsTo w.clock (Icc 0 T) I)
    {f : ℝ → E} (hf : ContinuousOn f I) : ContinuousOn (fun τ => f (w.clock τ)) (Icc 0 T) :=
  hf.comp (clock_continuous w).continuousOn hclock

/-! ## The normalized coefficient bounds from (2.6), (2.7), (2.8) -/

/-- The definition (2.6) of `δ` and the smallness (2.7) give the normalized bounds used
throughout Subsection 2.2: `ε ≤ 1/2`, `δ ≥ 0`, (2.8) (`S⁻¹ ≤ 2δ`, `S ≥ T² ≥ 1`), the
bound `240δT⁶ ≤ 1`, and at each time of the window the bounds on the quantities (2.9)
for the normalized older strain `B/r` and error `E_c/r` (`|b_ij| ≤ δ`,
`|2Sb₁₂ - 1| ≤ δ`, `|2Sb₃₂ - ε| ≤ δ`, `|E_c|/r ≤ δ/S`;
`sections/03_amplification.tex:201-263` and `:296-300`). The orthonormality of the frame
at `t₀` is the hypothesis `he₀` (the proof of Lemma 2.4 takes it from Lemma 2.2, the other
proofs from `basis_orthonormal`). -/
theorem normalized_facts (w : PhysicalAmplification I t₀) {T : ℝ} {C₀ : ℕ}
    (he₀ : Orthonormal ℝ (w.basis t₀))
    (hT : 2 ≤ T) (hC₀ : 240 ≤ C₀) (hs : FiniteSmallness w T C₀) :
    0 < w.ratio ∧ w.ratio ≤ 1 / 2 ∧ 0 ≤ w.errorSize ∧ 0 < w.shear ∧ 1 ≤ w.shear ∧
      w.shear⁻¹ ≤ 2 * w.errorSize ∧ (w.shear ^ 2)⁻¹ ≤ 2 * w.errorSize ∧
      240 * w.errorSize * T ^ 6 ≤ 1 ∧ T * w.errorSize ≤ 1 ∧ T ^ 2 ≤ w.shear ∧
      ∀ t ∈ I, ‖(1 / w.rate) • w.B t‖ ≤ w.errorSize ∧
        ‖(1 / w.rate) • w.E t‖ ≤ w.errorSize / w.shear ∧
        |2 * w.shear * entry (w.basis t) ((1 / w.rate) • w.B t) 0 1 - 1| ≤ w.errorSize ∧
        |2 * w.shear * entry (w.basis t) ((1 / w.rate) • w.B t) 2 1 - w.ratio| ≤
          w.errorSize := by
  have hε := amplification_epsilon_le_half (by omega : 2 ≤ C₀) w.ratio_pos.le hs.1
  have hnorm := normalized_rates_of_physical_error (t₀ := t₀) (σ := w.initialStrength)
    (e := w.basis) (B := w.B) (E := w.E) w.compact w.activation he₀ (basis_continuousOn w)
    w.older_continuous w.error_continuous w.initialStrength_pos
    w.first_coupling_positive w.third_coupling_positive (hε.trans (by norm_num))
  have hδ : 0 ≤ w.errorSize := hnorm.1
  have hinv : w.shear⁻¹ ≤ 2 * w.errorSize := hnorm.2.1
  have hshear : 0 < w.shear := div_pos w.initialStrength_pos w.rate_pos
  obtain ⟨-, h240, hTδ, hTS⟩ :=
    amplification_normalized_smallness hT hδ w.ratio_pos.le hshear hinv hC₀ hs.1 hs.2
  have hS1 : 1 ≤ w.shear := (show 1 ≤ T ^ 2 by nlinarith [sq_nonneg (T - 2)]).trans hTS
  have hinv2 : (w.shear ^ 2)⁻¹ ≤ 2 * w.errorSize := by
    rw [← inv_pow]
    have hS₁ : w.shear⁻¹ ≤ 1 := (inv_le_one₀ hshear).mpr hS1
    exact (by nlinarith only [mul_nonneg (inv_nonneg.mpr hshear.le) (sub_nonneg.mpr hS₁)] :
      w.shear⁻¹ ^ 2 ≤ w.shear⁻¹).trans hinv
  exact ⟨w.ratio_pos, hε, hδ, hshear, hS1, hinv, hinv2, h240, hTδ, hTS,
    fun t ht => hnorm.2.2 t ht⟩

/-- The smallness (2.7) absorbs any fixed polynomial `C T^p δ` into `ε` and into `1/2`,
for `C₀` large. -/
theorem absorb {T δ ε C : ℝ} {p C₀ : ℕ} (hT : 2 ≤ T) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hp : p ≤ C₀) (hC₀ : 2 * C ≤ C₀) (hsmall : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε) (hε : ε ≤ 1) :
    C * T ^ p * δ ≤ 1 / 2 := by
  have h := amplification_absorb_power (by linarith : (1 : ℝ) ≤ T) hδ (by positivity : 0 ≤ 2 * C)
    hp hC₀ hsmall
  nlinarith

/-! ## The scaled components and the library coordinates -/

/-- The frame of the preceding wave in normalized time `τ`. -/
abbrev nbasis (w : PhysicalAmplification I t₀) : ℝ → Fin 3 → Space :=
  fun τ => w.basis (w.clock τ)

/-- `ζ₁ = X`. -/
theorem zeta_zero (w : PhysicalAmplification I t₀) (lam : ℝ) (k : ℝ → Space) (τ : ℝ) :
    zeta w lam k τ 0 = X (nbasis w) (k ∘ w.clock) lam τ := rfl

/-- `ζ₂ = Q`. -/
theorem zeta_one (w : PhysicalAmplification I t₀) (lam : ℝ) (k : ℝ → Space) (τ : ℝ) :
    zeta w lam k τ 1 = Q (nbasis w) (k ∘ w.clock) lam w.shear τ := rfl

/-- `ζ₃ = Z`. -/
theorem zeta_two (w : PhysicalAmplification I t₀) (lam : ℝ) (k : ℝ → Space) (τ : ℝ) :
    zeta w lam k τ 2 = Z (nbasis w) (k ∘ w.clock) lam τ := rfl

/-- `α₁ = -U`. -/
theorem alpha_zero (w : PhysicalAmplification I t₀) (a : ℝ → Space) (τ : ℝ) :
    alpha w a τ 0 = -U (nbasis w) (a ∘ w.clock) w.shear τ := by
  change w.shear * ⟪w.basis (w.clock τ) 0, a (w.clock τ)⟫_ℝ =
    -(-w.shear * ⟪w.basis (w.clock τ) 0, a (w.clock τ)⟫_ℝ)
  ring

/-- `α₂ = V`. -/
theorem alpha_one (w : PhysicalAmplification I t₀) (a : ℝ → Space) (τ : ℝ) :
    alpha w a τ 1 = V (nbasis w) (a ∘ w.clock) τ := rfl

/-- The components of `ζ₀ = (tan φ, -ετ, 1)`. -/
theorem zetaRef_apply (ε τ : ℝ) :
    zetaRef ε τ 0 = x ε τ ∧ zetaRef ε τ 1 = -(ε * τ) ∧ zetaRef ε τ 2 = 1 :=
  ⟨tan_referenceAngle_eq_x ε τ, rfl, rfl⟩

/-- A component of a vector of `ℝ³` is bounded by its Euclidean norm. -/
theorem abs_apply_le_norm (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have h := PiLp.norm_apply_le v i
  simpa only [Real.norm_eq_abs] using h

/-- The Euclidean bound `|ζ - ζ₀| ≤ d` gives the three coordinate bounds of the library. -/
theorem coordinates_close_of_zeta (w : PhysicalAmplification I t₀) {lam : ℝ}
    {k : ℝ → Space} {τ d : ℝ} (h : ‖zeta w lam k τ - zetaRef w.ratio τ‖ ≤ d) :
    |X (nbasis w) (k ∘ w.clock) lam τ - x w.ratio τ| ≤ d ∧
      |Q (nbasis w) (k ∘ w.clock) lam w.shear τ + w.ratio * τ| ≤ d ∧
      |Z (nbasis w) (k ∘ w.clock) lam τ - 1| ≤ d := by
  obtain ⟨h0, h1, h2⟩ := zetaRef_apply w.ratio τ
  refine ⟨?_, ?_, ?_⟩
  · have := (abs_apply_le_norm (zeta w lam k τ - zetaRef w.ratio τ) 0).trans h
    simpa only [PiLp.sub_apply, zeta_zero, h0] using this
  · have := (abs_apply_le_norm (zeta w lam k τ - zetaRef w.ratio τ) 1).trans h
    simpa only [PiLp.sub_apply, zeta_one, h1, sub_neg_eq_add] using this
  · have := (abs_apply_le_norm (zeta w lam k τ - zetaRef w.ratio τ) 2).trans h
    simpa only [PiLp.sub_apply, zeta_two, h2] using this

/-- A positive third scaled component `ζ₃` forces `k ≠ 0`. -/
theorem ne_zero_of_zeta_two_pos (w : PhysicalAmplification I t₀) {lam : ℝ} {k : ℝ → Space}
    {τ : ℝ} (h : 0 < zeta w lam k τ 2) : k (w.clock τ) ≠ 0 := by
  intro h0
  rw [zeta_two] at h
  simp only [Z, Function.comp_apply, h0, inner_zero_right, zero_div, lt_self_iff_false] at h

/-- The couplings `ν₊ = E₁,₊·ME₂,₊` and `η₊ = E₃,₊·ME₂,₊` of the new wave are continuous in
`τ` on `[0, T]` where `k` and `a` are nonzero. -/
theorem continuousOn_physicalCouplings (w : PhysicalAmplification I t₀) {T : ℝ}
    (hclock : MapsTo w.clock (Icc 0 T) I) {k a : ℝ → Space}
    (hk : ContinuousOn k I) (ha : ContinuousOn a I)
    (hk₀ : ∀ τ ∈ Icc 0 T, k (w.clock τ) ≠ 0) (ha₀ : ∀ τ ∈ Icc 0 T, a (w.clock τ) ≠ 0) :
    ContinuousOn (fun τ => w.physicalNu k a (w.clock τ)) (Icc 0 T) ∧
      ContinuousOn (fun τ => w.physicalEta k a (w.clock τ)) (Icc 0 T) := by
  have hKn := continuousOn_normalize (continuousOn_comp_clock w hclock hk) hk₀
  have hAn := continuousOn_normalize (continuousOn_comp_clock w hclock ha) ha₀
  have hM := continuousOn_comp_clock w hclock (gradient_continuousOn w)
  exact ⟨hKn.inner (hM.clm_apply hAn), (continuousOn_cross3 hKn hAn).inner (hM.clm_apply hAn)⟩

/-! ## The couplings in normalized time -/

/-- The normalized strain `B/r + Sσ_p/σ E₂⊗E₁ + E_c/r` of the library at normalized time
`τ` is the full physical gradient `M` at `t₀ + τ/r` divided by `r`. -/
theorem normalizedStrain_eq (w : PhysicalAmplification I t₀) {τ : ℝ} (hτ : w.clock τ ∈ I) :
    strain (nbasis w τ) ((1 / w.rate) • w.B (w.clock τ)) ((1 / w.rate) • w.E (w.clock τ))
        w.shear (strengthRatio (w.kp ∘ w.clock) (w.ap ∘ w.clock) τ) =
      (1 / w.rate) • w.gradient (w.clock τ) := by
  obtain ⟨hk₀, ha₀, _⟩ := w.preceding_data t₀ w.activation
  obtain ⟨hk, ha, _⟩ := w.preceding_data (w.clock τ) hτ
  have h := normalized_strain_eq
    (kp := fun s => w.kp (w.clock s)) (ap := fun s => w.ap (w.clock s))
    (B := w.B (w.clock τ)) (E := w.E (w.clock τ)) w.rate_pos.ne'
    (by simpa only [PhysicalAmplification.clock_zero] using hk₀)
    (by simpa only [PhysicalAmplification.clock_zero] using ha₀) hk ha
  simp only [PhysicalAmplification.clock_zero] at h
  simp only [PhysicalAmplification.shear, PhysicalAmplification.initialStrength,
    PhysicalAmplification.gradient]
  exact h

/-- The library's normalized couplings at normalized time `τ` are the physical couplings
`ν₊ = E₁,₊·ME₂,₊` and `η₊ = E₃,₊·ME₂,₊` at `t₀ + τ/r` divided by `ν`. -/
theorem normalizedCouplings_eq (w : PhysicalAmplification I t₀) {τ : ℝ} (hτ : w.clock τ ∈ I)
    (k a : ℝ → Space) :
    let M := strain (nbasis w τ) ((1 / w.rate) • w.B (w.clock τ))
      ((1 / w.rate) • w.E (w.clock τ)) w.shear
      (strengthRatio (w.kp ∘ w.clock) (w.ap ∘ w.clock) τ)
    GrowingCoupling.normalizedNu M (k (w.clock τ)) (a (w.clock τ)) w.shear =
        w.physicalNu k a (w.clock τ) / w.firstCoupling ∧
      GrowingCoupling.normalizedEta M (k (w.clock τ)) (a (w.clock τ)) w.shear =
        w.physicalEta k a (w.clock τ) / w.firstCoupling := by
  have hr_sq : w.rate ^ 2 = 2 * w.initialStrength * w.firstCoupling :=
    amplificationGrowthRate_sq w.initialStrength_pos w.first_coupling_positive
  have hf : 2 * w.shear * (1 / w.rate) = 1 / w.firstCoupling := by
    calc
      _ = 2 * w.initialStrength / w.rate ^ 2 := by
        unfold PhysicalAmplification.shear
        field_simp
      _ = _ := by
        rw [hr_sq]; field_simp [w.initialStrength_pos.ne', w.first_coupling_positive.ne']
  have hf_apply (b : ℝ) : 2 * w.shear * ((1 / w.rate) * b) = b / w.firstCoupling := by
    rw [← mul_assoc, hf, one_div_mul_eq_div]
  dsimp only
  rw [normalizedStrain_eq w hτ]
  constructor <;> simp only [GrowingCoupling.normalizedNu, GrowingCoupling.normalizedEta,
    smul_apply, real_inner_smul_right, hf_apply,
    PhysicalAmplification.physicalNu, PhysicalAmplification.physicalEta]

/-- The strength ratio `σ_p/σ` in normalized time. -/
theorem strengthRatio_clock (w : PhysicalAmplification I t₀) (τ : ℝ) :
    strengthRatio (w.kp ∘ w.clock) (w.ap ∘ w.clock) τ =
      ‖w.kp (w.clock τ)‖ * ‖w.ap (w.clock τ)‖ / w.initialStrength := by
  simp only [strengthRatio, Function.comp_apply, PhysicalAmplification.clock_zero,
    PhysicalAmplification.initialStrength]

/-! ## The conjugation `P = diag(-1, 1)` -/

/-- `P(u, v) = (-u, v)`. -/
def flipCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (-(ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- `P(u, v) = (-u, v)`, pointwise. -/
@[simp] theorem flipCLM_apply (p : ℝ × ℝ) : flipCLM p = (-p.1, p.2) := rfl

/-- `‖P‖ ≤ 1`. -/
theorem norm_flipCLM_le : ‖flipCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  simp only [flipCLM_apply, one_mul, Prod.norm_def, norm_neg]
  exact le_rfl

/-- The library error matrix `R = PℰP` attached to the error `ℰ` of Lemma 2.4. -/
def conjError (ℰ : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (τ : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  flipCLM.comp ((ℰ τ).comp flipCLM)

/-- `‖PℰP‖ ≤ ‖ℰ‖`. -/
theorem norm_conjError_le (ℰ : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (τ : ℝ) :
    ‖conjError ℰ τ‖ ≤ ‖ℰ τ‖ := by
  unfold conjError
  calc
    _ ≤ ‖flipCLM‖ * (‖ℰ τ‖ * ‖flipCLM‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖ℰ τ‖ * 1) := by
      gcongr
      · exact norm_flipCLM_le
      · exact norm_flipCLM_le
    _ = _ := by ring

/-- Continuity of `ℰ` gives continuity of `PℰP`. -/
theorem continuousOn_conjError {J : Set ℝ} {ℰ : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h : ContinuousOn ℰ J) : ContinuousOn (conjError ℰ) J := by
  unfold conjError
  have h1 : ContinuousOn (fun τ => (ℰ τ).comp flipCLM) J :=
    ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)).flip flipCLM).continuous.comp_continuousOn h
  exact ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)) flipCLM).continuous.comp_continuousOn h1

/-- The first component of a derivative in `ℝ × ℝ`. -/
theorem hasDerivWithinAt_fst {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {J : Set ℝ} {τ : ℝ}
    (h : HasDerivWithinAt f f' J τ) : HasDerivWithinAt (fun s => (f s).1) f'.1 J τ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt τ h

/-- The second component of a derivative in `ℝ × ℝ`. -/
theorem hasDerivWithinAt_snd {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {J : Set ℝ} {τ : ℝ}
    (h : HasDerivWithinAt f f' J τ) : HasDerivWithinAt (fun s => (f s).2) f'.2 J τ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt τ h

/-- The system of Lemma 2.4 for `(α₁, α₂)` is the library's raw system for
`(U, V) = (-α₁, α₂)` with error matrix `PℰP`. -/
theorem raw_system_of_alpha (w : PhysicalAmplification I t₀) {a : ℝ → Space}
    {ℰ : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {J : Set ℝ} {τ : ℝ}
    (h : HasDerivWithinAt (fun s => (alpha w a s 0, alpha w a s 1))
      (pairOperator (referenceSystemMatrix w.ratio τ) (alpha w a τ 0, alpha w a τ 1) +
        ℰ τ (alpha w a τ 0, alpha w a τ 1)) J τ) :
    let u := U (nbasis w) (a ∘ w.clock) w.shear
    let v := V (nbasis w) (a ∘ w.clock)
    HasDerivWithinAt u (-damping w.ratio τ * u τ + driving w.ratio τ * v τ +
      (conjError ℰ τ (u τ, v τ)).1) J τ ∧
    HasDerivWithinAt v (u τ + (conjError ℰ τ (u τ, v τ)).2) J τ := by
  intro u v
  have hu : u = fun s => -alpha w a s 0 := by
    funext s; rw [alpha_zero, neg_neg]
  have hv : v = fun s => alpha w a s 1 := by
    funext s; rw [alpha_one]
  obtain ⟨h00, h01, h10, h11⟩ := referenceSystemMatrix_apply w.ratio τ
  have hfst := hasDerivWithinAt_fst h
  have hsnd := hasDerivWithinAt_snd h
  simp only [Prod.fst_add, Prod.snd_add, pairOperator_apply,
    h00, h01, h10, h11] at hfst hsnd
  have hp : (u τ, v τ) = flipCLM (alpha w a τ 0, alpha w a τ 1) := by
    simp only [hu, hv, flipCLM_apply]
  have hflip : flipCLM (u τ, v τ) = (alpha w a τ 0, alpha w a τ 1) := by
    simp only [hu, hv, flipCLM_apply, neg_neg]
  have hR : conjError ℰ τ (u τ, v τ) = flipCLM (ℰ τ (alpha w a τ 0, alpha w a τ 1)) := by
    simp only [conjError, ContinuousLinearMap.comp_apply, hflip]
  rw [hR]
  constructor
  · rw [hu]
    refine hfst.neg.congr_deriv ?_
    simp only [hv, flipCLM_apply]
    ring
  · rw [hv]
    refine hsnd.congr_deriv ?_
    simp only [hu, flipCLM_apply]
    ring

end

end TorusEuler.Paper.Lib.S2b
