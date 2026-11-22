import PhyslibAlpha.Mathematics.PartialDerivativeTest

open Nat ContinuousMultilinearMap Finset Function

/-- The little-o form of the second-derivative test holds without the smoothness hypothesis:
the proof of `isLocalMin_of_posDef_of_littleo` with its use of that hypothesis removed. -/
theorem isLocalMin_of_posDef_of_littleo_without_smoothness {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {f : V → ℝ} {x₀ : V}
    (h : (fun x => f x - ∑ i ∈ range 3, 1 / (i)! * iteratedFDeriv ℝ i f x₀ fun _ => x - x₀)
      =o[nhds x₀] fun x => ‖x - x₀‖ ^ 2) (h₀ : gradient f x₀ = 0)
    (hf : (iteratedFDerivQuadraticMap f x₀).PosDef) : IsLocalMin f x₀ := by
  have ⟨C,hC⟩ := coercive_of_posdef hf
  simp only [Asymptotics.IsLittleO, Asymptotics.IsBigOWith] at h
  apply (h (half_pos hC.1)).mono
  intro x
  have hx := hC.2 (x - x₀)
  simp only [continuousBilinearMapOfContinuousMultilinearMap, MultilinearMap.toFun_eq_coe,
    coe_coe, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk] at hx
  rw [mul_assoc,show ![x - x₀, x - x₀] = fun _ => x - x₀ by
    ext i; fin_cases i <;> simp] at hx
  have hx₀ : inner ℝ (gradient f x₀) (x - x₀) = fderiv ℝ f x₀ (x - x₀) := by simp [gradient]
  simp only [h₀, inner_zero_left, map_sub] at hx₀
  simp only [norm_pow, norm_norm]
  rw [← pow_two] at hx
  exact le_of_littleO hx <| sub_eq_zero.mp hx₀.symm
