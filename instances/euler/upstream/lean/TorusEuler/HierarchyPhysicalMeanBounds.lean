import TorusEuler.HierarchyPhysicalSolvers
import TorusEuler.HierarchyPhaseIndependentNorm

/-! The actual mixed seminorm bound for the physical mean selected by the
ordered hierarchy. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

set_option maxHeartbeats 2300000 in
/-- The same physical mean solve used at each level satisfies the one-derivative
estimate in the hierarchy's unweighted mixed seminorm. The phase scale is
arbitrary because both the mean source and the mean output are independent of
the phase. -/
theorem exists_physicalSolvers_meanSeminormBound (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ (p s₀ : ℕ) (C : ℕ → ℝ), (∀ n, 0 ≤ C n) ∧
      ∀ {T D : ℝ} {κ₀ : Vec3} {U : Velocity} {X : ℝ → Velocity}
        (hT : 0 < T) (hT₁ : T ≤ 1), 2 ≤ D →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
      ∀ (G M : HierarchyTwistedProfile T κ₀ (Vec3 →L[ℝ] Vec3))
        (κ : HierarchyTwistedProfile T κ₀ Vec3) (d : MeanCoefficients G M),
      d.inverse_bound ≤ D → d.strain_bound ≤ D →
      (∀ t ∈ Icc 0 T, ∀ a, d.deformation (t, toUnitTorus a) = fderiv ℝ (X 0 t) a) →
      (∀ t ∈ Icc 0 T, ∀ a, d.strain (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a)) →
      ∀ (osc : TransverseCoefficients M κ) (s : ℕ), s₀ ≤ s →
      ∀ (h : ℝ) (n : ℕ) (S : HierarchyTwistedProfile T κ₀ Vec3)
        (hS : (twistedHierarchyOperators hT G M κ).average S = S),
        let ℓ := (D ^ s)⁻¹
        let solvers := physicalSolvers hT hT₁ G M κ d osc
        unweightedSeminorm False ℓ h n hT (solvers.solveMean S hS).val.B ≤
          C n * D ^ (p + 2 + 2 * s) * unweightedSeminorm False ℓ h (n + 1) hT S := by
  obtain ⟨p, s₀, C, hC, hBound⟩ := exists_solveMean_labelNormBound R hR
  refine ⟨p, s₀, C, hC, ?_⟩
  intro T D κ₀ U X hT hT₁ hD hX hU hUper hF₀ hG₀ hUjets G M κ d hD₀ hLD hF hM osc s hs h n S hS
  let ℓ := (D ^ s)⁻¹
  let out := solveMean hT hT₁ G M κ d S hS
  let B := out.output.B
  change unweightedSeminorm False ℓ h n hT B ≤
    C n * D ^ (p + 2 + 2 * s) * unweightedSeminorm False ℓ h (n + 1) hT S
  rw [unweightedSeminorm_false_eq_labelWordNorm_of_average hT ℓ h n B out.output.average_B,
      unweightedSeminorm_false_eq_labelWordNorm_of_average hT ℓ h (n + 1) S hS]
  exact hBound hT hT₁ hD hX hU hUper hF₀ hG₀ hUjets G M κ d hD₀ hLD hF hM S hS s hs n

end

end TorusEuler.HierarchyTwistedProfile
