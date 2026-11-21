import TorusEuler.MovingAmplitudeCoefficients

/-! The reference substitution in Lemma 2.3, using the strain entries and
reciprocals that occur in the polynomial expressions for the amplitude rows. -/

namespace TorusEuler.MovingAmplitude

noncomputable section

/-- Put the three rescaled strain entries in their original matrix positions. -/
def scaledEntries (A : Entries) (S : ℝ) : Entries :=
  !![A 0 0, S * A 0 1, A 0 2;
     A 1 0 / S, A 1 1, A 1 2;
     A 2 0, S * A 2 1, A 2 2]

def scaledNormFactor (X Q Z invS : ℝ) : ℝ :=
  X ^ 2 + Q ^ 2 * invS ^ 2 + Z ^ 2

theorem scaledNormFactor_eq (X Q Z S : ℝ) :
    scaledNormFactor X Q Z S⁻¹ = normFactor X Q Z S := by
  simp only [scaledNormFactor, normFactor, div_eq_mul_inv, inv_pow]

def scaledPressureU {R : Type*} [CommRing R] (A : Fin 3 → Fin 3 → R) (X Q Z invS invZ : R) : R :=
  X * (-A 0 0 + A 0 2 * X * invZ) +
    Q * (-A 1 0 + A 1 2 * invS * X * invZ) +
    Z * (-A 2 0 + A 2 2 * X * invZ)

def scaledPressureV {R : Type*} [CommRing R] (A : Fin 3 → Fin 3 → R) (X Q Z invS invZ : R) : R :=
  X * (A 0 1 - A 0 2 * Q * invZ) +
    Q * (A 1 1 - A 1 2 * invS * Q * invZ) +
    Z * (A 2 1 - A 2 2 * Q * invZ)

theorem scaledPressureU_eq (A : Entries) (X Q Z S : ℝ) :
    scaledPressureU (scaledEntries A S) X Q Z S⁻¹ Z⁻¹ = pressureU A X Q Z S := by
  simp only [scaledPressureU, pressureU, scaledEntries, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_mul_inv]
  ring

theorem scaledPressureV_eq (A : Entries) (X Q Z S : ℝ) :
    scaledPressureV (scaledEntries A S) X Q Z S⁻¹ Z⁻¹ = pressureV A X Q Z S := by
  simp only [scaledPressureV, pressureV, scaledEntries, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_mul_inv]

/-- The amplitude rows are polynomials in the scaled entries, wave coordinates
and reciprocals. At a physical state, the final three inputs are (S^{-1}),
(Z^{-1}) and (m^{-1}). -/
def scaledMatrix {R : Type*} [CommRing R] (b A : Fin 3 → Fin 3 → R)
    (X Q Z invS invZ invM : R) : Matrix (Fin 2) (Fin 2) R :=
  let fu := scaledPressureU A X Q Z invS invZ
  let fv := scaledPressureV A X Q Z invS invZ
  !![-A 0 0 + (A 0 2 + b 0 2) * X * invZ - 2 * X * fu * invM,
     A 0 1 + b 0 1 - (A 0 2 + b 0 2) * Q * invZ - 2 * X * fv * invM;
     A 1 0 - b 0 1 * invS ^ 2 - (A 1 2 + b 2 1 * invS) * invS * X * invZ +
       2 * Q * fu * invS ^ 2 * invM,
     -A 1 1 + (A 1 2 + b 2 1 * invS) * invS * Q * invZ + 2 * Q * fv * invS ^ 2 * invM]

theorem scaledMatrix_eq (b A : Entries) (X Q Z S : ℝ) (hS : S ≠ 0) (hZ : Z ≠ 0) :
    scaledMatrix (scaledEntries b S) (scaledEntries A S) X Q Z S⁻¹ Z⁻¹
      (normFactor X Q Z S)⁻¹ = rawMatrix b A X Q Z S := by
  have hM : normFactor X Q Z S ≠ 0 := by
    unfold normFactor
    have := sq_pos_of_ne_zero hZ
    positivity
  unfold scaledMatrix rawMatrix
  simp only [scaledPressureU_eq, scaledPressureV_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [scaledEntries, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    field_simp

def referenceScaledOlderEntries (ε : ℝ) : Entries :=
  !![0, 1 / 2, 0; 0, 0, 0; 0, ε / 2, 0]

def referenceScaledStrainEntries (ε : ℝ) : Entries :=
  !![0, 1 / 2, 0; 1, 0, 0; 0, ε / 2, 0]

open ReferenceRiccati (x s s_sq_mul damping driving)

/-- The three reference values in the pressure part of Lemma 2.3. -/
theorem scaledPressure_reference (ε τ : ℝ) :
    scaledPressureU (referenceScaledStrainEntries ε) (x ε τ) (-ε * τ) 1 0 1 = ε * τ ∧
    scaledPressureV (referenceScaledStrainEntries ε) (x ε τ) (-ε * τ) 1 0 1 = (x ε τ + ε) / 2 ∧
    scaledNormFactor (x ε τ) (-ε * τ) 1 0 = 1 + x ε τ ^ 2 := by
  constructor
  · norm_num [scaledPressureU, referenceScaledStrainEntries, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  constructor
  · norm_num [scaledPressureV, referenceScaledStrainEntries, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · simp [scaledNormFactor, add_comm]

/-- The limiting values of the scaled inputs give the matrix of (2.6). -/
theorem scaledMatrix_reference (ε τ : ℝ) :
    scaledMatrix (referenceScaledOlderEntries ε) (referenceScaledStrainEntries ε)
      (x ε τ) (-ε * τ) 1 0 1 (s ε τ ^ 2) = referenceMatrix ε τ := by
  obtain ⟨hU, hV, _⟩ := scaledPressure_reference ε τ
  unfold scaledMatrix referenceMatrix
  simp only [hU, hV]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [referenceScaledOlderEntries, referenceScaledStrainEntries, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, damping, driving] <;>
    ring_nf
  linear_combination -(s_sq_mul ε τ)

end

end TorusEuler.MovingAmplitude
