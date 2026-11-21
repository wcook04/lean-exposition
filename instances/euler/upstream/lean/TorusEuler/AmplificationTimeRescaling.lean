import TorusEuler.MovingCoordinateWaveVector

/-! Rescaling the affine-wave equations to the time variable of Lemma 2.3. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.MovingWaveVector

/-- The inverse clock sends the whole normalized time interval into the original interval. -/
theorem mapsTo_amplificationTime_Icc {r t₀ T : ℝ} (hr : 0 < r) :
    MapsTo (fun τ => t₀ + τ / r) (Icc 0 T) (Icc t₀ (t₀ + T / r)) := by
  intro τ hτ
  exact ⟨le_add_of_nonneg_right (div_nonneg hτ.1 hr.le),
    add_le_add_right (div_le_div_of_nonneg_right hτ.2 hr.le) t₀⟩

/-- Both affine-wave equations retain their form in the normalized time,
with the strain divided by the growth rate. -/
theorem normalized_affineWave_derivatives {k a : ℝ → Space} {I J : Set ℝ}
    {D : Space →L[ℝ] Space} {r t₀ τ : ℝ}
    (hmap : MapsTo (fun t => t₀ + t / r) J I)
    (hk : HasDerivWithinAt k (-(D.adjoint (k (t₀ + τ / r)))) I (t₀ + τ / r))
    (ha : let u := t₀ + τ / r
      HasDerivWithinAt a (-(D (a u)) + (2 * ⟪k u, D (a u)⟫_ℝ / ‖k u‖ ^ 2) • k u) I u) :
    let u := t₀ + τ / r
    let D' := (1 / r) • D
    HasDerivWithinAt (fun t => k (t₀ + t / r)) (-(D'.adjoint (k u))) J τ ∧
      HasDerivWithinAt (fun t => a (t₀ + t / r))
        (-(D' (a u)) + (2 * ⟪k u, D' (a u)⟫_ℝ / ‖k u‖ ^ 2) • k u) J τ := by
  dsimp only
  refine ⟨(hasDerivWithinAt_normalized_time hmap hk).congr_deriv ?_,
    (hasDerivWithinAt_normalized_time hmap ha).congr_deriv ?_⟩
  · simp only [map_smul, smul_apply, smul_neg]
  · simp only [smul_apply, real_inner_smul_right, smul_add, smul_neg, smul_smul]
    congr 2
    ring

/-- The new wave in physical time solves the normalized equations with the
older strain, shear and error in the form used by the moving-coordinate lemmas. -/
theorem normalized_newWave_derivatives {kp ap k a : ℝ → Space} {I J : Set ℝ}
    {B E : Space →L[ℝ] Space} {r t₀ τ : ℝ}
    (hr : r ≠ 0) (hmap : MapsTo (fun t => t₀ + t / r) J I)
    (hkp₀ : kp t₀ ≠ 0) (hap₀ : ap t₀ ≠ 0)
    (hkp : kp (t₀ + τ / r) ≠ 0) (hap : ap (t₀ + τ / r) ≠ 0)
    (hk : let u := t₀ + τ / r
      let M := B + InnerProductSpace.rankOne ℝ (ap u) (kp u) + E
      HasDerivWithinAt k (-(M.adjoint (k u))) I u)
    (ha : let u := t₀ + τ / r
      let M := B + InnerProductSpace.rankOne ℝ (ap u) (kp u) + E
      HasDerivWithinAt a (-(M (a u)) + (2 * ⟪k u, M (a u)⟫_ℝ / ‖k u‖ ^ 2) • k u) I u) :
    let u := t₀ + τ / r
    let kp' (t : ℝ) := kp (t₀ + t / r)
    let ap' (t : ℝ) := ap (t₀ + t / r)
    let S := (‖kp t₀‖ * ‖ap t₀‖) / r
    let M := strain (frame kp' ap' τ) ((1 / r) • B) ((1 / r) • E)
      S (strengthRatio kp' ap' τ)
    HasDerivWithinAt (fun t => k (t₀ + t / r)) (-(M.adjoint (k u))) J τ ∧
      HasDerivWithinAt (fun t => a (t₀ + t / r))
        (-(M (a u)) + (2 * ⟪k u, M (a u)⟫_ℝ / ‖k u‖ ^ 2) • k u) J τ := by
  let kp' (t : ℝ) := kp (t₀ + t / r)
  let ap' (t : ℝ) := ap (t₀ + t / r)
  have hkp₀' : kp' 0 ≠ 0 := by simpa [kp'] using hkp₀
  have hap₀' : ap' 0 ≠ 0 := by simpa [ap'] using hap₀
  have hM := normalized_strain_eq (kp := kp') (ap := ap') (B := B) (E := E) hr
    hkp₀' hap₀' (show kp' τ ≠ 0 from hkp) (show ap' τ ≠ 0 from hap)
  simp only [kp', ap', zero_div, add_zero] at hM
  dsimp only at hk ha ⊢
  rw [hM]
  exact normalized_affineWave_derivatives hmap hk ha

/-- Rescaling preserves the trace-free hypothesis of the preceding-frame equation. -/
theorem normalized_trace_zero {B : Space →L[ℝ] Space} {r : ℝ}
    (hB : LinearMap.trace ℝ Space B.toLinearMap = 0) :
    LinearMap.trace ℝ Space (((1 / r) • B).toLinearMap) = 0 := by
  rw [ContinuousLinearMap.toLinearMap_smul, map_smul, hB, smul_zero]

private theorem shearScale_div_growth {r σ ν : ℝ} (hr : 0 < r) (hσ : 0 < σ)
    (hν : 0 < ν) (hr₂ : r ^ 2 = 2 * σ * ν) :
    (σ / r) * (1 / r) = 1 / (2 * ν) := by
  calc
    _ = σ / r ^ 2 := by field_simp
    _ = _ := by rw [hr₂]; field_simp

/-- The factor `2*S` converts a normalized strain entry into its ratio to `ν`. -/
theorem normalized_coupling_entry {r σ ν : ℝ} (hr : 0 < r) (hσ : 0 < σ)
    (hν : 0 < ν) (hr₂ : r ^ 2 = 2 * σ * ν) (e : Fin 3 → Space)
    (B : Space →L[ℝ] Space) (i j : Fin 3) :
    2 * (σ / r) * entry e ((1 / r) • B) i j = entry e B i j / ν := by
  rw [entry, smul_apply, real_inner_smul_right, ← mul_assoc, mul_assoc 2,
    shearScale_div_growth hr hσ hν hr₂, entry]
  field_simp

/-- The normalized matrix error with one factor of shear has norm
`‖E‖ / (2*ν)`, the coefficient size used in Lemma 2.3. -/
theorem normalized_shear_error_norm {r σ ν : ℝ} (hr : 0 < r) (hσ : 0 < σ)
    (hν : 0 < ν) (hr₂ : r ^ 2 = 2 * σ * ν) (E : Space →L[ℝ] Space) :
    (σ / r) * ‖(1 / r) • E‖ = ‖E‖ / (2 * ν) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← mul_assoc,
    shearScale_div_growth hr hσ hν hr₂, one_div_mul_eq_div]

end TorusEuler.MovingWaveVector
