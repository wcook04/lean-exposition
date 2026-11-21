import TorusEuler.Paper.Proofs.S2b.Library.Glue

/-! # Normalized time for the proof of Lemma 2.4

Glue for the proof of Lemma 2.4 (namespace `TorusEuler.Paper.Lib.S2b`): the equations of
the new wave in normalized time `τ` (`t = t₀ + τ/r`, `sections/03_amplification.tex:289-300`),
the passage from the library's raw system for `(U, V) = (-α₁, α₂)` to the system of
Lemma 2.4 for `(α₁, α₂)`, the Euclidean norms of `ζ - ζ₀` and `ζ`, and the elementary
estimate behind the second bound of (2.10).
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S2b

open MovingWaveVector MovingAmplitude ReferenceRiccati

noncomputable section

variable {I : Set ℝ} {t₀ : ℝ}

/-- The normalized strain `B/r + Sσ_p/σ E₂⊗E₁ + E_c/r` at normalized time `τ`. -/
abbrev nstrain (w : PhysicalAmplification I t₀) (τ : ℝ) : Space →L[ℝ] Space :=
  strain (nbasis w τ) ((1 / w.rate) • w.B (w.clock τ)) ((1 / w.rate) • w.E (w.clock τ))
    w.shear (strengthRatio (w.kp ∘ w.clock) (w.ap ∘ w.clock) τ)

/-- The wave vector of the new wave in normalized time: `K' = -Mᵀ K/r`. -/
theorem rescale_waveVector (w : PhysicalAmplification I t₀) {T lam : ℝ}
    (hclock : MapsTo w.clock (Icc 0 T) I) {k : ℝ → Space} (hk : NewWaveVector w lam k)
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    HasDerivWithinAt (k ∘ w.clock) (-((nstrain w τ).adjoint ((k ∘ w.clock) τ))) (Icc 0 T) τ := by
  rw [nstrain, normalizedStrain_eq w (hclock hτ)]
  have h := hasDerivWithinAt_normalized_time hclock (hk.2.2 _ (hclock hτ))
  refine h.congr_deriv ?_
  simp only [map_smul, smul_apply, smul_neg, Function.comp_apply]
  rfl

/-- An amplitude vector in normalized time: `A' = -MA/r + p_w K` with the normalized
strain. -/
theorem rescale_amplitude (w : PhysicalAmplification I t₀) {T lam : ℝ}
    (hclock : MapsTo w.clock (Icc 0 T) I) {k a : ℝ → Space} (hk : NewWaveVector w lam k)
    (ha : AmplitudeVector w k a) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    HasDerivWithinAt (a ∘ w.clock)
      (-(nstrain w τ ((a ∘ w.clock) τ)) +
        (2 * ⟪(k ∘ w.clock) τ, nstrain w τ ((a ∘ w.clock) τ)⟫_ℝ / ‖(k ∘ w.clock) τ‖ ^ 2) •
          (k ∘ w.clock) τ) (Icc 0 T) τ := by
  rw [nstrain, normalizedStrain_eq w (hclock hτ)]
  exact (normalized_affineWave_derivatives hclock (hk.2.2 _ (hclock hτ))
    (ha.1 _ (hclock hτ))).2

/-- The library's raw system for `(U, V) = (-α₁, α₂)` with error matrix `R` is the system
of Lemma 2.4 for `(α₁, α₂)` with error `PRP`. -/
theorem alpha_system_of_raw (w : PhysicalAmplification I t₀) {a : ℝ → Space}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {J : Set ℝ} {τ : ℝ}
    (hU : HasDerivWithinAt (U (nbasis w) (a ∘ w.clock) w.shear)
      (-damping w.ratio τ * U (nbasis w) (a ∘ w.clock) w.shear τ +
        driving w.ratio τ * V (nbasis w) (a ∘ w.clock) τ +
        (R τ (U (nbasis w) (a ∘ w.clock) w.shear τ, V (nbasis w) (a ∘ w.clock) τ)).1) J τ)
    (hV : HasDerivWithinAt (V (nbasis w) (a ∘ w.clock))
      (U (nbasis w) (a ∘ w.clock) w.shear τ +
        (R τ (U (nbasis w) (a ∘ w.clock) w.shear τ, V (nbasis w) (a ∘ w.clock) τ)).2) J τ) :
    HasDerivWithinAt (fun s => (alpha w a s 0, alpha w a s 1))
      (pairOperator (referenceSystemMatrix w.ratio τ) (alpha w a τ 0, alpha w a τ 1) +
        conjError R τ (alpha w a τ 0, alpha w a τ 1)) J τ := by
  set u := U (nbasis w) (a ∘ w.clock) w.shear with hu
  set v := V (nbasis w) (a ∘ w.clock) with hv
  have hfun : (fun s => (alpha w a s 0, alpha w a s 1)) = fun s => (-u s, v s) := by
    funext s
    rw [alpha_zero, alpha_one]
  have h0 : alpha w a τ 0 = -u τ := alpha_zero w a τ
  have h1 : alpha w a τ 1 = v τ := alpha_one w a τ
  obtain ⟨h00, h01, h10, h11⟩ := referenceSystemMatrix_apply w.ratio τ
  rw [hfun, h0, h1]
  refine (hU.neg.prodMk hV).congr_deriv ?_
  simp only [conjError, ContinuousLinearMap.comp_apply, flipCLM_apply, neg_neg, pairOperator_apply,
    h00, h01, h10, h11, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- The Euclidean norm of `ζ - ζ₀` is at most the sum of the three coordinate errors. -/
theorem norm_zeta_sub_le (w : PhysicalAmplification I t₀) (lam : ℝ) (k : ℝ → Space)
    (τ : ℝ) :
    ‖zeta w lam k τ - zetaRef w.ratio τ‖ ≤
      |X (nbasis w) (k ∘ w.clock) lam τ - x w.ratio τ| +
        |Q (nbasis w) (k ∘ w.clock) lam w.shear τ + w.ratio * τ| +
        |Z (nbasis w) (k ∘ w.clock) lam τ - 1| := by
  obtain ⟨h0, h1, h2⟩ := zetaRef_apply w.ratio τ
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs, ← zeta_zero, ← zeta_one, ← zeta_two,
    h0, h1, h2]
  have h := euclidean_error_le_sum (zeta w lam k τ 0 - x w.ratio τ)
    (zeta w lam k τ 1 - -(w.ratio * τ)) (zeta w lam k τ 2 - 1)
  simpa only [sub_neg_eq_add] using h

/-- `|ζ| ≤ 3T²` from `|X| ≤ T²`, `|Q| ≤ T` and `Z ≤ 3/2`, the bound (2.11). -/
theorem norm_zeta_le (w : PhysicalAmplification I t₀) {lam T τ : ℝ} {k : ℝ → Space}
    (hT : 2 ≤ T) (hX : |X (nbasis w) (k ∘ w.clock) lam τ| ≤ T ^ 2)
    (hQ : |Q (nbasis w) (k ∘ w.clock) lam w.shear τ| ≤ T)
    (hZ₀ : 1 / 2 ≤ Z (nbasis w) (k ∘ w.clock) lam τ)
    (hZ₁ : Z (nbasis w) (k ∘ w.clock) lam τ ≤ 3 / 2) :
    ‖zeta w lam k τ‖ ≤ 3 * T ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, ← zeta_zero, ← zeta_one, ← zeta_two] at hX hQ hZ₀ hZ₁ ⊢
  have hX2 : zeta w lam k τ 0 ^ 2 ≤ T ^ 4 := by
    have := sq_le_sq' (abs_le.mp hX).1 (abs_le.mp hX).2
    nlinarith
  have hQ2 : zeta w lam k τ 1 ^ 2 ≤ T ^ 2 := sq_le_sq' (abs_le.mp hQ).1 (abs_le.mp hQ).2
  have hZ2 : zeta w lam k τ 2 ^ 2 ≤ 9 / 4 := by nlinarith
  have hT2 : 4 ≤ T ^ 2 := by nlinarith
  have hT4 : T ^ 2 ≤ T ^ 4 := by nlinarith
  calc
    _ ≤ Real.sqrt ((3 * T ^ 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = _ := Real.sqrt_sq (by positivity)

/-- `cos²φ = (1 + x²)⁻¹`. -/
theorem cos_referenceAngle_sq (ε τ : ℝ) :
    Real.cos (referenceAngle ε τ) ^ 2 = (1 + x ε τ ^ 2)⁻¹ := by
  rw [cos_referenceAngle, s, inv_pow, Real.sq_sqrt (by positivity)]

/-- The elementary estimate behind the second bound of (2.10): with
`m = X² + Q²/S² + Z²`, `|m/(1 + x²) - 1| ≤ 2T²e₀ + 2T²δ` when `|X - x|, |Z - 1| ≤ e₀ ≤ 1/2`,
`|Q| ≤ T`, `S⁻² ≤ 2δ` and `0 ≤ x ≤ T²/4`. -/
theorem normFactor_cos_bound {X Q Z x S T δ e₀ : ℝ} (hT : 2 ≤ T)
    (hS2 : (S ^ 2)⁻¹ ≤ 2 * δ) (hx0 : 0 ≤ x) (hxT : x ≤ T ^ 2 / 4)
    (hXx : |X - x| ≤ e₀) (he₀ : e₀ ≤ 1 / 2) (hQ : |Q| ≤ T) (hZ : |Z - 1| ≤ e₀) :
    |(X ^ 2 + Q ^ 2 / S ^ 2 + Z ^ 2) * (1 + x ^ 2)⁻¹ - 1| ≤ 2 * T ^ 2 * e₀ + 2 * T ^ 2 * δ := by
  have hT2 : 4 ≤ T ^ 2 := by nlinarith
  have hc0 : 0 < 1 + x ^ 2 := by positivity
  have hc1 : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hcpos : 0 < (1 + x ^ 2)⁻¹ := inv_pos.mpr hc0
  have he0 : 0 ≤ e₀ := (abs_nonneg _).trans hXx
  have hXp : |X + x| ≤ T ^ 2 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hXx
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hd : |X ^ 2 - x ^ 2| ≤ e₀ * T ^ 2 := by
    rw [show X ^ 2 - x ^ 2 = (X - x) * (X + x) by ring, abs_mul]
    exact mul_le_mul hXx hXp (abs_nonneg _) he0
  have hZp : |Z + 1| ≤ T ^ 2 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hZ
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hz : |Z ^ 2 - 1| ≤ e₀ * T ^ 2 := by
    rw [show Z ^ 2 - 1 = (Z - 1) * (Z + 1) by ring, abs_mul]
    exact mul_le_mul hZ hZp (abs_nonneg _) he0
  have hQ2 : Q ^ 2 ≤ T ^ 2 := sq_le_sq' (abs_le.mp hQ).1 (abs_le.mp hQ).2
  have hq0 : 0 ≤ Q ^ 2 / S ^ 2 := by positivity
  have hq : Q ^ 2 / S ^ 2 ≤ T ^ 2 * (2 * δ) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hQ2 hS2 (by positivity) (by positivity)
  have hm : |X ^ 2 + Q ^ 2 / S ^ 2 + Z ^ 2 - (1 + x ^ 2)| ≤ 2 * T ^ 2 * e₀ + 2 * T ^ 2 * δ := by
    have heq : X ^ 2 + Q ^ 2 / S ^ 2 + Z ^ 2 - (1 + x ^ 2) =
        (X ^ 2 - x ^ 2) + Q ^ 2 / S ^ 2 + (Z ^ 2 - 1) := by ring
    rw [heq]
    calc
      _ ≤ |X ^ 2 - x ^ 2| + |Q ^ 2 / S ^ 2| + |Z ^ 2 - 1| := abs_add_three _ _ _
      _ ≤ e₀ * T ^ 2 + T ^ 2 * (2 * δ) + e₀ * T ^ 2 := by
        rw [abs_of_nonneg hq0]; linarith
      _ = _ := by ring
  have heq : (X ^ 2 + Q ^ 2 / S ^ 2 + Z ^ 2) * (1 + x ^ 2)⁻¹ - 1 =
      (X ^ 2 + Q ^ 2 / S ^ 2 + Z ^ 2 - (1 + x ^ 2)) * (1 + x ^ 2)⁻¹ := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hcpos]
  calc
    _ ≤ |X ^ 2 + Q ^ 2 / S ^ 2 + Z ^ 2 - (1 + x ^ 2)| * 1 :=
      mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact hm

end

end TorusEuler.Paper.Lib.S2b
