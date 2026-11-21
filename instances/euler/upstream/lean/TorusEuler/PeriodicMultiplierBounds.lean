import TorusEuler.TorusLerayModes
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! The Leray projection on the Fourier modes in Appendix A. -/

open MeasureTheory UnitAddTorus
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

/-- The orthogonal complement of the complex span of the real wave vector.
At frequency zero this subspace is the entire coefficient space. -/
def transverseModeSpace (k : Fin 3 → ℤ) : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) :=
  (ℂ ∙ WithLp.toLp 2 (complexFrequency k))ᗮ

/-- The continuous linear Leray symbol on complex Euclidean coefficients. -/
def lerayModeProjection (k : Fin 3 → ℤ) :
    EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  (transverseModeSpace k).starProjection

private theorem inner_frequency (k : Fin 3 → ℤ) (a : ComplexVec3) :
    ⟪WithLp.toLp 2 (complexFrequency k), WithLp.toLp 2 a⟫_ℂ = frequencyContraction k a := by
  rw [PiLp.inner_apply]
  simp [frequencyContraction, complexFrequency, RCLike.inner_apply, mul_comm]

private theorem norm_sq_frequency (k : Fin 3 → ℤ) :
    ‖(WithLp.toLp 2 (complexFrequency k) : EuclideanSpace ℂ (Fin 3))‖ ^ 2 = frequencyNormSq k := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [frequencyNormSq, complexFrequency, Complex.norm_intCast, sq_abs]

theorem mem_transverseModeSpace_iff (k : Fin 3 → ℤ) (a : ComplexVec3) :
    (WithLp.toLp 2 a : EuclideanSpace ℂ (Fin 3)) ∈ transverseModeSpace k ↔
      frequencyContraction k a = 0 := by
  rw [transverseModeSpace, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_frequency]

theorem lerayModeProjection_toLp (k : Fin 3 → ℤ) (a : ComplexVec3) :
    lerayModeProjection k (WithLp.toLp 2 a) = WithLp.toLp 2 (lerayMode k a) := by
  change (ℂ ∙ (WithLp.toLp 2 (complexFrequency k) : EuclideanSpace ℂ (Fin 3)))ᗮ.starProjection
    (WithLp.toLp 2 a) = _
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
    inner_frequency, norm_sq_frequency]
  rfl

@[simp] theorem lerayModeProjection_zero : lerayModeProjection 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro a
  change lerayModeProjection 0 (WithLp.toLp 2 a.ofLp) = WithLp.toLp 2 a.ofLp
  rw [lerayModeProjection_toLp, lerayMode_zero]

theorem norm_lerayModeProjection_le (k : Fin 3 → ℤ) : ‖lerayModeProjection k‖ ≤ 1 :=
  (transverseModeSpace k).starProjection_norm_le

theorem inner_lerayModeProjection_left_eq_right (k : Fin 3 → ℤ)
    (a b : EuclideanSpace ℂ (Fin 3)) :
    ⟪lerayModeProjection k a, b⟫_ℂ = ⟪a, lerayModeProjection k b⟫_ℂ :=
  (transverseModeSpace k).inner_starProjection_left_eq_right a b

theorem norm_lerayMode_toLp_le (k : Fin 3 → ℤ) (a : ComplexVec3) :
    ‖(WithLp.toLp 2 (lerayMode k a) : EuclideanSpace ℂ (Fin 3))‖ ≤
    ‖(WithLp.toLp 2 a : EuclideanSpace ℂ (Fin 3))‖ := by
  rw [← lerayModeProjection_toLp]
  exact (transverseModeSpace k).norm_starProjection_apply_le _

section FourierEnergy

local instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem integral_inner_fourier_smul (k j : Fin 3 → ℤ) (a b : E) :
    (∫ z, ⟪mFourier k z • a, mFourier j z • b⟫_ℂ ∂unitTorusMeasure) =
      if k = j then ⟪a, b⟫_ℂ else 0 := by
  classical
  simp_rw [inner_smul_left, inner_smul_right, ← mFourier_neg, ← mul_assoc]
  rw [integral_mul_const, integral_fourier_pair]
  split <;> simp_all

/-- Finite Parseval identity for periodic trigonometric polynomials with
complex Hilbert-space coefficients. -/
theorem integral_inner_finiteFourierSum (s : Finset (Fin 3 → ℤ))
    (a b : (Fin 3 → ℤ) → E) :
    (∫ z, ⟪finiteFourierSum s a z, finiteFourierSum s b z⟫_ℂ ∂unitTorusMeasure) =
      ∑ k ∈ s, ⟪a k, b k⟫_ℂ := by
  classical
  have hInt (k j : Fin 3 → ℤ) :
      Integrable (fun z => ⟪mFourier k z • a k, mFourier j z • b j⟫_ℂ) unitTorusMeasure :=
    (((mFourier k).continuous.smul continuous_const).inner
      ((mFourier j).continuous.smul continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp_rw [finiteFourierSum, sum_inner, inner_sum]
  rw [integral_finsetSum s (fun k _ => integrable_finsetSum s (fun j _ => hInt k j))]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum s (fun j _ => hInt k j)]
  simp_rw [integral_inner_fourier_smul, eq_comm (a := k)]
  rw [Finset.sum_ite_eq' s k]
  simp [hk]

theorem integral_norm_sq_finiteFourierSum (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → E) :
    (∫ z, ‖finiteFourierSum s a z‖ ^ 2 ∂unitTorusMeasure) = ∑ k ∈ s, ‖a k‖ ^ 2 := by
  have hC : Continuous (finiteFourierSum s a) := by
    exact continuous_finsetSum s (fun k _ => (mFourier k).continuous.smul continuous_const)
  have hI : Integrable
      (fun z => ⟪finiteFourierSum s a z, finiteFourierSum s a z⟫_ℂ) unitTorusMeasure :=
    (hC.inner hC).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [integral_re hI, integral_inner_finiteFourierSum]
  exact map_sum Complex.reCLM _ _

/-- The Leray multiplier is L²-contractive on finite trigonometric polynomials. -/
theorem integral_norm_sq_leray_finiteFourierSum_le (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → EuclideanSpace ℂ (Fin 3)) :
    (∫ z, ‖finiteFourierSum s (fun k => lerayModeProjection k (a k)) z‖ ^ 2 ∂unitTorusMeasure) ≤
      ∫ z, ‖finiteFourierSum s a z‖ ^ 2 ∂unitTorusMeasure := by
  rw [integral_norm_sq_finiteFourierSum, integral_norm_sq_finiteFourierSum]
  exact Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _)
    ((transverseModeSpace k).norm_starProjection_apply_le (a k)) 2

/-- Testing the projected polynomial against a transverse polynomial preserves
the spatial L² pairing, as used in Appendix A's coercivity estimate. -/
theorem integral_inner_leray_finiteFourierSum_of_transverse
    (s : Finset (Fin 3 → ℤ)) (a b : (Fin 3 → ℤ) → EuclideanSpace ℂ (Fin 3))
    (hb : ∀ k ∈ s, b k ∈ transverseModeSpace k) :
    (∫ z, ⟪finiteFourierSum s (fun k => lerayModeProjection k (a k)) z,
      finiteFourierSum s b z⟫_ℂ ∂unitTorusMeasure) =
      ∫ z, ⟪finiteFourierSum s a z, finiteFourierSum s b z⟫_ℂ ∂unitTorusMeasure := by
  rw [integral_inner_finiteFourierSum, integral_inner_finiteFourierSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [inner_lerayModeProjection_left_eq_right]
  exact congrArg (inner ℂ (a k)) (Submodule.starProjection_eq_self_iff.mpr (hb k hk))

end FourierEnergy

end

end TorusEuler
