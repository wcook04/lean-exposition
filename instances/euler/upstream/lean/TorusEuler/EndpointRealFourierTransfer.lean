import TorusEuler.EndpointMixedProjection
import TorusEuler.FreezingConcreteMultipliers

/-! The real-character and complex Fourier formulations of the endpoint multiplier law. -/

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "ν" => unitTorusMeasure

local instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)))

variable {H HC : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup HC] [NormedSpace ℂ HC] [CompleteSpace HC]

omit [CompleteSpace H] [CompleteSpace HC] in
private theorem smul_complexification_ofReal (X : EndpointComplexification H HC)
    (c : ℂ) (v : H) :
    c • X.ofReal v = X.ofReal (c.re • v) + Complex.I • X.ofReal (c.im • v) := by
  calc
    _ = (c.re : ℂ) • X.ofReal v + Complex.I • ((c.im : ℂ) • X.ofReal v) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_comm _ Complex.I, mul_smul]
    _ = _ := by
      rw [X.ofReal.map_smul, X.ofReal.map_smul]
      exact congrArg₂ (· + ·)
        (RCLike.real_smul_eq_coe_smul (K := ℂ) c.re (X.ofReal v)).symm
        (congrArg (Complex.I • ·)
          (RCLike.real_smul_eq_coe_smul (K := ℂ) c.im (X.ofReal v)).symm)

/-- The real and imaginary parts of a complexified real field's Fourier
coefficient are its two real-character moments at the same mode. -/
theorem complexifiedHalfHolderFourierCoeff_realCharacterMoments
    (X : EndpointComplexification H HC) (f : HalfHolder Labels H) (k : Fin 3 → ℤ) :
    X.re (complexifiedHalfHolderFourierCoeff X f k) =
      (∫ a, endpointRealFourierCharacter k 1 a • HalfHolder.eval a f ∂ν) ∧
    X.im (complexifiedHalfHolderFourierCoeff X f k) =
      (∫ a, endpointRealFourierCharacter k Complex.I a • HalfHolder.eval a f ∂ν) := by
  let g := continuousHalfHolder (HalfHolder.map X.ofReal f)
  have hint : Integrable (fun a => mFourier (-k) a • g a) ν :=
    ((mFourier (-k)).continuous.smul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint (a : Labels) :
      mFourier (-k) a • g a =
        X.ofReal (endpointRealFourierCharacter k 1 a • HalfHolder.eval a f) +
          Complex.I • X.ofReal
            (endpointRealFourierCharacter k Complex.I a • HalfHolder.eval a f) := by
    change mFourier (-k) a • HalfHolder.eval a (HalfHolder.map X.ofReal f) = _
    rw [HalfHolder.eval_map, smul_complexification_ofReal, mFourier_neg]
    have hre : (conj (mFourier k a)).re = endpointRealFourierCharacter k 1 a := by
      change (conj (mFourier k a)).re = (1 * mFourier k a).re
      rw [Complex.conj_re, one_mul]
    have him : (conj (mFourier k a)).im = endpointRealFourierCharacter k Complex.I a := by
      change (conj (mFourier k a)).im = (Complex.I * mFourier k a).re
      simp only [Complex.conj_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_sub]
    rw [hre, him]
  change X.re (∫ a, mFourier (-k) a • g a ∂ν) = _ ∧
    X.im (∫ a, mFourier (-k) a • g a ∂ν) = _
  constructor
  · rw [← X.re.integral_comp_comm hint]
    apply integral_congr_ae
    exact ae_of_all _ fun a => by
      change X.re (mFourier (-k) a • g a) = _
      rw [hpoint a, map_add, X.re_ofReal, X.re_I, X.im_ofReal, neg_zero, add_zero]
  · rw [← X.im.integral_comp_comm hint]
    apply integral_congr_ae
    exact ae_of_all _ fun a => by
      change X.im (mFourier (-k) a • g a) = _
      rw [hpoint a, map_add, X.im_ofReal, X.im_I, X.re_ofReal, zero_add]

/-- A real operator acting on real-character moments acts on the complex
coefficient by its complex-linear extension. -/
theorem complexifiedHalfHolderFourierCoeff_eq_apply_of_realCharacterMoments
    (X : EndpointComplexification H HC) {f g : HalfHolder Labels H}
    (k : Fin 3 → ℤ) (B : H →L[ℝ] H)
    (h : ∀ c : ℂ,
      (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a g ∂ν) =
        B (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a f ∂ν)) :
    complexifiedHalfHolderFourierCoeff X g k =
      X.extendOperator B (complexifiedHalfHolderFourierCoeff X f k) := by
  obtain ⟨hfr, hfi⟩ := complexifiedHalfHolderFourierCoeff_realCharacterMoments X f k
  obtain ⟨hgr, hgi⟩ := complexifiedHalfHolderFourierCoeff_realCharacterMoments X g k
  calc
    _ = X.ofReal (X.re (complexifiedHalfHolderFourierCoeff X g k)) +
        Complex.I • X.ofReal (X.im (complexifiedHalfHolderFourierCoeff X g k)) :=
      (X.reconstruct _).symm
    _ = _ := by
      rw [hgr, hgi, h 1, h Complex.I, ← hfr, ← hfi, X.extendOperator_apply]

/-- A multiplier law on real characters implies the complex Fourier law
for the same real half-Hölder operator. -/
theorem complexifiedHalfHolderFourierCoeff_multiplier_of_realCharacterMoments
    (X : EndpointComplexification H HC)
    (P : HalfHolder Labels H →L[ℝ] HalfHolder Labels H) (S : Vec3 → H →L[ℝ] H)
    (h : ∀ (f : HalfHolder Labels H) (k : Fin 3 → ℤ) (c : ℂ),
      (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a (P f) ∂ν) =
        S (latticeVector k) (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a f ∂ν))
    (f : HalfHolder Labels H) (k : Fin 3 → ℤ) :
    complexifiedHalfHolderFourierCoeff X (P f) k =
      X.extendOperator (S (latticeVector k)) (complexifiedHalfHolderFourierCoeff X f k) :=
  complexifiedHalfHolderFourierCoeff_eq_apply_of_realCharacterMoments X k _ (h f k)

end
end TorusEuler
