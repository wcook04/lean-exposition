import TorusEuler.MovingAmplitudeCoefficients
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! The contribution of the additional strain to the amplitude matrix of Lemma 2.3. -/

open scoped InnerProductSpace

namespace TorusEuler.MovingAmplitude

open MovingWaveVector

noncomputable section

private def coordinateWave (e : Fin 3 → Space) (x q z S : ℝ) : Space :=
  x • e 0 + (q / S) • e 1 + z • e 2

private def coordinateAmplitude (e : Fin 3 → Space) (x q z S u v : ℝ) : Space :=
  (-u / S) • e 0 + v • e 1 + ((x * u - q * v) / (S * z)) • e 2

private def amplitudeProjection (e : Fin 3 → Space) (S : ℝ) (w : Space) : ℝ × ℝ :=
  (-S * ⟪e 0, w⟫_ℝ, ⟪e 1, w⟫_ℝ)

private theorem coordinateWave_inner {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (x q z S : ℝ) :
    ⟪e 0, coordinateWave e x q z S⟫_ℝ = x ∧
    ⟪e 1, coordinateWave e x q z S⟫_ℝ = q / S ∧
    ⟪e 2, coordinateWave e x q z S⟫_ℝ = z := by
  have h := orthonormal_iff_ite.mp he
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [coordinateWave, inner_add_right, real_inner_smul_right, h, he.norm_eq_one]

private theorem norm_coordinateWave_sq {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (x q z S : ℝ) : ‖coordinateWave e x q z S‖ ^ 2 = normFactor x q z S := by
  obtain ⟨h₀, h₁, h₂⟩ := coordinateWave_inner he x q z S
  calc
    ‖coordinateWave e x q z S‖ ^ 2 =
      ⟪x • e 0 + (q / S) • e 1 + z • e 2, coordinateWave e x q z S⟫_ℝ :=
        (real_inner_self_eq_norm_sq _).symm
    _ = _ := by
      simp only [inner_add_left, real_inner_smul_left, h₀, h₁, h₂, normFactor]
      ring

private theorem coordinateAmplitude_strain_inner {e : Fin 3 → Space} (E : Space →L[ℝ] Space)
    (x q z S u v : ℝ) (i : Fin 3) :
    ⟪e i, E (coordinateAmplitude e x q z S u v)⟫_ℝ =
      (-u / S) * entry e E i 0 + v * entry e E i 1 +
        ((x * u - q * v) / (S * z)) * entry e E i 2 := by
  simp only [coordinateAmplitude, map_smul, map_add, inner_add_right,
    real_inner_smul_right, entry]

private theorem coordinatePressure {e : Fin 3 → Space} (E : Space →L[ℝ] Space)
    {x q z S u v : ℝ} (hS : S ≠ 0) (hz : z ≠ 0) :
    ⟪coordinateWave e x q z S, E (coordinateAmplitude e x q z S u v)⟫_ℝ =
      (pressureU (entry e E) x q z S * u + pressureV (entry e E) x q z S * v) / S := by
  simp only [coordinateWave, inner_add_left, real_inner_smul_left,
    coordinateAmplitude_strain_inner, pressureU, pressureV]
  field_simp
  ring

private theorem rawMatrix_zero_apply {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (E : Space →L[ℝ] Space) {x q z S u v : ℝ} (hS : S ≠ 0) (hz : z ≠ 0) :
    let k := coordinateWave e x q z S
    let w := E (coordinateAmplitude e x q z S u v)
    pairOperator (rawMatrix 0 (entry e E) x q z S) (u, v) =
      amplitudeProjection e S (-w + (2 * ⟪k, w⟫_ℝ / ‖k‖ ^ 2) • k) := by
  obtain ⟨h₀, h₁, _⟩ := coordinateWave_inner he x q z S
  have hm : normFactor x q z S ≠ 0 := by
    unfold normFactor
    have := sq_pos_of_ne_zero hz
    positivity
  dsimp only
  simp only [pairOperator_apply, amplitudeProjection, rawMatrix, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, add_zero, sub_zero,
    inner_add_right, inner_neg_right, real_inner_smul_right, h₀, h₁,
    coordinateAmplitude_strain_inner, coordinatePressure E hS hz, norm_coordinateWave_sq he]
  congr 1 <;> field_simp [hm] <;> ring

private theorem norm_coordinateAmplitude_le {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    {x q z S u v : ℝ} (hS : 1 ≤ S) (hx : |x| ≤ S) (hq : |q| ≤ S) (hz : 1 / 2 ≤ z) :
    ‖coordinateAmplitude e x q z S u v‖ ≤ 6 * ‖(u, v)‖ := by
  have hS₀ : 0 < S := zero_lt_one.trans_le hS
  have hz₀ : 0 < z := by linarith
  have hu : |u| ≤ ‖(u, v)‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le (u, v)
  have hv : |v| ≤ ‖(u, v)‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le (u, v)
  have hfirst : |-u / S| ≤ ‖(u, v)‖ := by
    rw [abs_div, abs_neg, abs_of_pos hS₀]
    exact (div_le_iff₀ hS₀).mpr (hu.trans (le_mul_of_one_le_right (norm_nonneg _) hS))
  have hthird : |(x * u - q * v) / (S * z)| ≤ 4 * ‖(u, v)‖ := by
    rw [abs_div, abs_of_pos (mul_pos hS₀ hz₀)]
    apply (div_le_iff₀ (mul_pos hS₀ hz₀)).mpr
    calc
      |x * u - q * v| ≤ |x * u| + |q * v| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (x * u) (q * v)
      _ ≤ S * ‖(u, v)‖ + S * ‖(u, v)‖ := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hx hu (abs_nonneg _) hS₀.le)
          (mul_le_mul hq hv (abs_nonneg _) hS₀.le)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hz (mul_nonneg hS₀.le (norm_nonneg (u, v)))
        nlinarith
  calc
    ‖coordinateAmplitude e x q z S u v‖ ≤
        ‖(-u / S) • e 0‖ + ‖v • e 1‖ + ‖((x * u - q * v) / (S * z)) • e 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = |-u / S| + |v| + |(x * u - q * v) / (S * z)| := by
      simp only [norm_smul, he.norm_eq_one, Real.norm_eq_abs, mul_one]
    _ ≤ 6 * ‖(u, v)‖ := by linarith

private theorem norm_amplitudeProjection_le {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    {S : ℝ} (hS : 1 ≤ S) (w : Space) : ‖amplitudeProjection e S w‖ ≤ S * ‖w‖ := by
  have hS₀ : 0 ≤ S := zero_le_one.trans hS
  have hi (i : Fin 3) : |⟪e i, w⟫_ℝ| ≤ ‖w‖ := by
    simpa only [he.norm_eq_one i, one_mul] using abs_real_inner_le_norm (e i) w
  simp only [amplitudeProjection, Prod.norm_def, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg hS₀, max_le_iff]
  exact ⟨mul_le_mul_of_nonneg_left (hi 0) hS₀,
    (hi 1).trans (le_mul_of_one_le_left (norm_nonneg _) hS)⟩

private theorem norm_reflected (k w : Space) :
    ‖-w + (2 * ⟪k, w⟫_ℝ / ‖k‖ ^ 2) • k‖ = ‖w‖ := by
  convert (Submodule.reflection (ℝ ∙ k)).norm_map w using 1
  congr 1
  rw [Submodule.reflection_singleton_apply, two_smul ℕ, ← two_smul ℝ, smul_smul,
    mul_div_assoc, sub_eq_neg_add]
  rfl

private theorem errorOperator_sub_strain (e : Fin 3 → Space) (B E : Space →L[ℝ] Space)
    (ε τ x q z S σratio : ℝ) :
    errorOperator ε τ (entry e B) (entry e (strain e B E S σratio)) x q z S -
      errorOperator ε τ (entry e B) (entry e (strain e B 0 S σratio)) x q z S =
      pairOperator (rawMatrix 0 (entry e E) x q z S) := by
  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  simp only [sub_apply, errorOperator, pairOperator_apply, Prod.mk_sub_mk, Matrix.sub_apply,
    rawMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, pressureU, pressureV,
    Pi.zero_apply, entry, strain, add_apply, add_zero, inner_add_right, sub_zero,
    div_eq_mul_inv]
  congr 1 <;> ring

/-- The strain perturbation contributes at most `6 * S * ‖E‖` to the error
operator of Lemma 2.3. Here `E` is already divided by the time scale `r`. -/
theorem norm_errorOperator_sub_strain_le {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (B E : Space →L[ℝ] Space) {ε τ x q z S σratio : ℝ}
    (hS : 1 ≤ S) (hx : |x| ≤ S) (hq : |q| ≤ S) (hz : 1 / 2 ≤ z) :
    ‖errorOperator ε τ (entry e B) (entry e (strain e B E S σratio)) x q z S -
      errorOperator ε τ (entry e B) (entry e (strain e B 0 S σratio)) x q z S‖ ≤ 6 * S * ‖E‖ := by
  have hS₀ : 0 < S := zero_lt_one.trans_le hS
  have hz₀ : 0 < z := by linarith
  rw [errorOperator_sub_strain]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  rintro ⟨u, v⟩
  rw [rawMatrix_zero_apply he E hS₀.ne' hz₀.ne']
  exact (norm_amplitudeProjection_le he hS _).trans (by
    rw [norm_reflected]
    calc
      _ ≤ S * (‖E‖ * ‖coordinateAmplitude e x q z S u v‖) :=
        mul_le_mul_of_nonneg_left (E.le_opNorm _) hS₀.le
      _ ≤ S * (‖E‖ * (6 * ‖(u, v)‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_coordinateAmplitude_le he hS hx hq hz)
            (norm_nonneg _)) hS₀.le
      _ = _ := by ring)

end

end TorusEuler.MovingAmplitude
