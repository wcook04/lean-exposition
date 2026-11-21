import TorusEuler.TorusFourier

/-!
Fourier symbols of the pressure inverse and Leray projection in the
unit-torus conventions of the paper.
-/

open MeasureTheory UnitAddTorus

namespace TorusEuler

noncomputable section

abbrev ComplexVec3 := Fin 3 → ℂ

/-- The integer wave vector as a complex coordinate vector. -/
def complexFrequency (k : Fin 3 → ℤ) : ComplexVec3 := fun i => (k i : ℂ)

/-- Its squared Euclidean length. -/
def frequencyNormSq (k : Fin 3 → ℤ) : ℝ := ∑ i, (k i : ℝ) ^ 2

/-- The contraction with the real wave vector, extended complex-linearly. -/
def frequencyContraction (k : Fin 3 → ℤ) (a : ComplexVec3) : ℂ :=
  ∑ i, complexFrequency k i * a i

theorem frequencyNormSq_pos {k : Fin 3 → ℤ} (hk : k ≠ 0) : 0 < frequencyNormSq k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have hki : (k i : ℝ) ≠ 0 := by exact_mod_cast hi
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hki⟩

@[simp] theorem frequencyContraction_zero (a : ComplexVec3) : frequencyContraction 0 a = 0 := by
  simp [frequencyContraction, complexFrequency]

@[simp] theorem frequencyContraction_complexFrequency (k : Fin 3 → ℤ) :
    frequencyContraction k (complexFrequency k) = (frequencyNormSq k : ℂ) := by
  simp [frequencyContraction, complexFrequency, frequencyNormSq, pow_two]

theorem frequencyContraction_smul (k : Fin 3 → ℤ) (c : ℂ) (a : ComplexVec3) :
    frequencyContraction k (c • a) = c * frequencyContraction k a := by
  simp only [frequencyContraction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem frequencyContraction_sub (k : Fin 3 → ℤ) (a b : ComplexVec3) :
    frequencyContraction k (a - b) = frequencyContraction k a - frequencyContraction k b := by
  simp only [frequencyContraction, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Leray's symbol acts as the identity on the zero frequency. In the
formula the length denominator has inverse zero at that frequency. -/
def lerayMode (k : Fin 3 → ℤ) (a : ComplexVec3) : ComplexVec3 :=
  a - (frequencyContraction k a / (frequencyNormSq k : ℂ)) • complexFrequency k

@[simp] theorem lerayMode_zero (a : ComplexVec3) : lerayMode 0 a = a := by
  simp [lerayMode]

theorem lerayMode_of_transverse {k : Fin 3 → ℤ} {a : ComplexVec3}
    (h : frequencyContraction k a = 0) : lerayMode k a = a := by
  simp [lerayMode, h]

theorem frequencyContraction_lerayMode (k : Fin 3 → ℤ) (a : ComplexVec3) :
    frequencyContraction k (lerayMode k a) = 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hnorm : (frequencyNormSq k : ℂ) ≠ 0 := by
      exact_mod_cast (frequencyNormSq_pos hk).ne'
    rw [lerayMode, frequencyContraction_sub, frequencyContraction_smul,
      frequencyContraction_complexFrequency, div_mul_cancel₀ _ hnorm, sub_self]

theorem lerayMode_idempotent (k : Fin 3 → ℤ) (a : ComplexVec3) :
    lerayMode k (lerayMode k a) = lerayMode k a := lerayMode_of_transverse (frequencyContraction_lerayMode k a)

/-- The symbol of the sum of second coordinate derivatives. -/
def laplacianMode (k : Fin 3 → ℤ) : ℂ :=
  -((2 * (Real.pi : ℂ)) ^ 2 * (frequencyNormSq k : ℂ))

/-- Inversion at nonzero frequency with the constant pressure set to zero. -/
def inverseLaplacianMode (k : Fin 3 → ℤ) : ℂ := (laplacianMode k)⁻¹

@[simp] theorem laplacianMode_zero : laplacianMode 0 = 0 := by
  simp [laplacianMode, frequencyNormSq]

@[simp] theorem inverseLaplacianMode_zero : inverseLaplacianMode 0 = 0 := by
  simp [inverseLaplacianMode]

theorem laplacianMode_ne_zero {k : Fin 3 → ℤ} (hk : k ≠ 0) : laplacianMode k ≠ 0 := by
  have hnorm : (frequencyNormSq k : ℂ) ≠ 0 := by
    exact_mod_cast (frequencyNormSq_pos hk).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hpi)) hnorm)

theorem laplacianMode_mul_inverseLaplacianMode (k : Fin 3 → ℤ) :
    laplacianMode k * inverseLaplacianMode k = if k = 0 then 0 else 1 := by
  classical
  by_cases hk : k = 0
  · simp [hk]
  · simp [inverseLaplacianMode, hk, laplacianMode_ne_zero hk]

/-- The symbol of the complex-linear divergence on a vector mode. -/
def divergenceMode (k : Fin 3 → ℤ) (a : ComplexVec3) : ℂ :=
  ∑ i, fourierDerivativeSymbol k i * a i

/-- The symbol of the gradient applied to a scalar mode. -/
def gradientMode (k : Fin 3 → ℤ) (b : ℂ) : ComplexVec3 :=
  fun i => fourierDerivativeSymbol k i * b

theorem divergenceMode_eq (k : Fin 3 → ℤ) (a : ComplexVec3) :
    divergenceMode k a = (2 * (Real.pi : ℂ) * Complex.I) * frequencyContraction k a := by
  simp only [divergenceMode, frequencyContraction, complexFrequency, fourierDerivativeSymbol,
    Finset.mul_sum, mul_assoc]

@[simp] theorem divergenceMode_zero (a : ComplexVec3) : divergenceMode 0 a = 0 := by
  rw [divergenceMode_eq, frequencyContraction_zero, mul_zero]

theorem divergenceMode_lerayMode (k : Fin 3 → ℤ) (a : ComplexVec3) :
    divergenceMode k (lerayMode k a) = 0 := by
  rw [divergenceMode_eq, frequencyContraction_lerayMode, mul_zero]

theorem divergenceMode_gradientMode (k : Fin 3 → ℤ) (b : ℂ) :
    divergenceMode k (gradientMode k b) = laplacianMode k * b := by
  unfold divergenceMode gradientMode laplacianMode frequencyNormSq
  push_cast
  rw [← neg_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [fourierDerivativeSymbol]
  calc
    _ = ((2 * (Real.pi : ℂ)) ^ 2 * Complex.I ^ 2 * (k i : ℂ) ^ 2) * b := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The scalar mode whose gradient is subtracted in the Leray projection. -/
def pressureCorrectionMode (k : Fin 3 → ℤ) (a : ComplexVec3) : ℂ :=
  inverseLaplacianMode k * divergenceMode k a

@[simp] theorem pressureCorrectionMode_zero (a : ComplexVec3) :
    pressureCorrectionMode 0 a = 0 := by
  simp [pressureCorrectionMode]

theorem lerayMode_eq_sub_gradient (k : Fin 3 → ℤ) (a : ComplexVec3) :
    lerayMode k a = a - gradientMode k (pressureCorrectionMode k a) := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let C : ℂ := (2 * (Real.pi : ℂ)) ^ 2
  have hc : c * c = -C := by
    change (2 * (Real.pi : ℂ) * Complex.I) * (2 * (Real.pi : ℂ) * Complex.I) =
      -((2 * (Real.pi : ℂ)) ^ 2)
    rw [← pow_two, mul_pow, Complex.I_sq, mul_neg_one]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hC : -C ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero two_ne_zero hpi))
  funext i
  simp only [lerayMode, gradientMode, pressureCorrectionMode, inverseLaplacianMode,
    divergenceMode_eq, laplacianMode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    complexFrequency, fourierDerivativeSymbol]
  congr 1
  change frequencyContraction k a / (frequencyNormSq k : ℂ) * (k i : ℂ) =
    c * (k i : ℂ) * ((-(C * (frequencyNormSq k : ℂ)))⁻¹ * (c * frequencyContraction k a))
  rw [← neg_mul, mul_inv_rev, div_eq_mul_inv]
  symm
  calc
    _ = (c * c) * (-C)⁻¹ * (frequencyContraction k a * (frequencyNormSq k : ℂ)⁻¹ *
        (k i : ℂ)) := by ring
    _ = _ := by rw [hc, mul_inv_cancel₀ hC, one_mul]

/-- Divergence on the complexified Euclidean lift in Cartesian coordinates. -/
def complexDivergence (v : Vec3 → ComplexVec3) (x : Vec3) : ℂ :=
  ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i 1)) i

/-- Gradient on the complexified Euclidean lift in Cartesian coordinates. -/
def complexGradient (p : Vec3 → ℂ) (x : Vec3) : ComplexVec3 :=
  fun i => fderiv ℝ p x (EuclideanSpace.single i 1)

/-- The sum of the second coordinate derivatives. -/
def complexLaplacian (p : Vec3 → ℂ) : Vec3 → ℂ := complexDivergence (complexGradient p)

theorem complexDivergence_lift_finiteFourierSum
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexVec3) (x : Vec3) :
    complexDivergence (fun y => finiteFourierSum s a (toUnitTorus y)) x =
      finiteFourierSum s (fun k => divergenceMode k (a k)) (toUnitTorus x) := by
  unfold complexDivergence
  simp_rw [fderiv_lift_finiteFourierSum_single]
  unfold finiteFourierSum divergenceMode
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem complexGradient_lift_finiteFourierSum
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ) (x : Vec3) :
    complexGradient (fun y => finiteFourierSum s a (toUnitTorus y)) x =
      finiteFourierSum s (fun k => gradientMode k (a k)) (toUnitTorus x) := by
  funext i
  rw [complexGradient, fderiv_lift_finiteFourierSum_single]
  simp only [finiteFourierSum, gradientMode, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem complexLaplacian_lift_finiteFourierSum
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ) (x : Vec3) :
    complexLaplacian (fun y => finiteFourierSum s a (toUnitTorus y)) x =
      finiteFourierSum s (fun k => laplacianMode k * a k) (toUnitTorus x) := by
  unfold complexLaplacian
  have hg : complexGradient (fun y => finiteFourierSum s a (toUnitTorus y)) =
      fun y => finiteFourierSum s (fun k => gradientMode k (a k)) (toUnitTorus y) :=
    funext (complexGradient_lift_finiteFourierSum s a)
  rw [hg, complexDivergence_lift_finiteFourierSum]
  simp_rw [divergenceMode_gradientMode]

theorem integral_lift_finiteFourierSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) :
    (∫ x in centeredCell, finiteFourierSum s a (toUnitTorus x)) =
      if 0 ∈ s then a 0 else 0 := by
  classical
  rw [← mFourierCoeff_finiteFourierSum, fourierCoeff_eq_centeredCell]
  simp [fourierMode, mFourier_zero]

/-- The finite-mode pressure inverse recovers the source with its zero
frequency removed. -/
theorem complexLaplacian_lift_inverseLaplacianMode
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ) (x : Vec3) :
    complexLaplacian
      (fun y => finiteFourierSum s (fun k => inverseLaplacianMode k * a k) (toUnitTorus y)) x =
      finiteFourierSum s (fun k => if k = 0 then 0 else a k) (toUnitTorus x) := by
  classical
  rw [complexLaplacian_lift_finiteFourierSum]
  congr with k
  rw [← mul_assoc, laplacianMode_mul_inverseLaplacianMode]
  split_ifs <;> simp

theorem integral_lift_inverseLaplacianMode
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ) :
    (∫ x in centeredCell,
      finiteFourierSum s (fun k => inverseLaplacianMode k * a k) (toUnitTorus x)) = 0 := by
  classical
  rw [integral_lift_finiteFourierSum]
  simp

theorem integral_lift_pressureCorrectionMode
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexVec3) :
    (∫ x in centeredCell,
      finiteFourierSum s (fun k => pressureCorrectionMode k (a k)) (toUnitTorus x)) = 0 :=
  integral_lift_inverseLaplacianMode _ _

theorem complexDivergence_lift_lerayMode
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexVec3) (x : Vec3) :
    complexDivergence
      (fun y => finiteFourierSum s (fun k => lerayMode k (a k)) (toUnitTorus y)) x = 0 := by
  rw [complexDivergence_lift_finiteFourierSum]
  simp [finiteFourierSum, divergenceMode_lerayMode]

theorem lift_lerayMode_eq_sub_gradient
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexVec3) (x : Vec3) :
    finiteFourierSum s (fun k => lerayMode k (a k)) (toUnitTorus x) =
      finiteFourierSum s a (toUnitTorus x) -
        complexGradient
          (fun y => finiteFourierSum s (fun k => pressureCorrectionMode k (a k)) (toUnitTorus y)) x := by
  rw [complexGradient_lift_finiteFourierSum]
  simp only [finiteFourierSum, lerayMode_eq_sub_gradient, smul_sub, Finset.sum_sub_distrib]

theorem complexLaplacian_lift_pressureCorrectionMode
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexVec3) (x : Vec3) :
    complexLaplacian
      (fun y => finiteFourierSum s (fun k => pressureCorrectionMode k (a k)) (toUnitTorus y)) x =
      complexDivergence (fun y => finiteFourierSum s a (toUnitTorus y)) x := by
  unfold pressureCorrectionMode
  rw [complexLaplacian_lift_inverseLaplacianMode, complexDivergence_lift_finiteFourierSum]
  congr with k
  split_ifs with hk
  · simp [hk]
  · rfl

theorem integral_lift_lerayMode
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexVec3) :
    (∫ x in centeredCell,
      finiteFourierSum s (fun k => lerayMode k (a k)) (toUnitTorus x)) =
      ∫ x in centeredCell, finiteFourierSum s a (toUnitTorus x) := by
  rw [integral_lift_finiteFourierSum, integral_lift_finiteFourierSum, lerayMode_zero]

theorem complexDivergence_lift_finiteFourierSum_eq_zero_iff
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexVec3) :
    (∀ x, complexDivergence (fun y => finiteFourierSum s a (toUnitTorus y)) x = 0) ↔
      ∀ k ∈ s, divergenceMode k (a k) = 0 := by
  classical
  simp_rw [complexDivergence_lift_finiteFourierSum]
  constructor
  · intro h k hk
    have hz : finiteFourierSum s (fun j => divergenceMode j (a j)) = 0 := by
      funext z
      obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
      exact h x
    have hcoeff := mFourierCoeff_finiteFourierSum s (fun j => divergenceMode j (a j)) k
    rw [hz] at hcoeff
    simp only [hk, ite_true] at hcoeff
    simpa [mFourierCoeff] using hcoeff.symm
  · intro h x
    unfold finiteFourierSum
    exact Finset.sum_eq_zero fun k hk => by simp [h k hk]

theorem divergenceMode_real_smul (k : Fin 3 → ℤ) (c : ℝ) (a : ComplexVec3) :
    divergenceMode k (c • a) = c • divergenceMode k a := by
  simp only [divergenceMode, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The cutoff preserves divergence freeness for a trigonometric
polynomial. -/
theorem complexDivergence_lift_smoothFourierCutoff_finiteFourierSum
    (ψ : Vec3 → ℝ) (Λ : ℝ) (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → ComplexVec3)
    (h : ∀ x, complexDivergence (fun y => finiteFourierSum s a (toUnitTorus y)) x = 0)
    (x : Vec3) :
    complexDivergence
      (fun y => smoothFourierCutoff ψ Λ (finiteFourierSum s a) (toUnitTorus y)) x = 0 := by
  classical
  have hmode := (complexDivergence_lift_finiteFourierSum_eq_zero_iff s a).mp h
  unfold smoothFourierCutoff
  apply (complexDivergence_lift_finiteFourierSum_eq_zero_iff _ _).mpr _ x
  intro k _
  rw [divergenceMode_real_smul, mFourierCoeff_finiteFourierSum]
  split_ifs with hk
  · rw [hmode k hk, smul_zero]
  · simp [divergenceMode]

end

end TorusEuler
