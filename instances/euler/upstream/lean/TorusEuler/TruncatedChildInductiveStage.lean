import TorusEuler.InductiveStageConstruction
import TorusEuler.TruncatedChildStage

/-! The physical cutoff step as a stage of the dependent Euler induction. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

namespace InductiveEulerStage

/-- The cutoff child with the two scheduled bounds supplies the next physical stage. -/
def ofTruncatedChildStage {P : InductiveEulerParameters} {n : ℕ} {activation T Λ : ℝ}
    {ψ : Vec3 → ℝ} {V RV : Velocity} {Y : ℝ → Velocity}
    (s : TruncatedChildStage T Λ ψ V RV)
    (hSlab : T = P.slab n activation) (hRadius : Λ = P.frequency n ^ 5)
    (hU : ∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ P.frequency n)
    (hFlow : ChildFlow.DeformationOn s.velocity Y T (P.frequency n))
    (hR : ∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ P.frequency (n + 1) ^ (-3 : ℝ))
    (hP : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range n, (P.frequency i)⁻¹) * ‖v‖ ^ 2) :
    InductiveEulerStage P n activation := by
  subst T
  subst Λ
  refine {
    torusVelocity := s.torusVelocity
    pressure := s.pressure
    flow := Y
    smooth_velocity := s.smooth_velocity
    odd_velocity := s.odd_velocity
    divergence_free := s.divergence_free
    velocity_band := s.velocity_band
    velocity_bound := hU
    smooth_pressure := s.smooth_pressure
    periodic_pressure := s.periodic_pressure
    mean_zero_pressure := s.mean_zero_pressure
    poisson := s.poisson
    projected_eq := s.projected_eq
    residual_bound := ?_
    deformation := hFlow
    pressure_hessian := hP }
  intro t ht x
  have hpow : P.frequency (n + 1) ^ (-3 : ℝ) = ((P.frequency (n + 1))⁻¹)^3 := by
    calc
      _ = P.frequency (n + 1) ^ (-(3 : ℕ) : ℤ) := Real.rpow_neg_natCast _ 3
      _ = _ := by rw [zpow_neg, zpow_natCast, inv_pow]
  exact (hR t ht x).trans_eq hpow

@[simp] theorem ofTruncatedChildStage_velocity {P : InductiveEulerParameters} {n : ℕ}
    {activation T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity} {Y : ℝ → Velocity}
    (s : TruncatedChildStage T Λ ψ V RV)
    (hSlab : T = P.slab n activation) (hRadius : Λ = P.frequency n ^ 5)
    (hU : ∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ P.frequency n)
    (hFlow : ChildFlow.DeformationOn s.velocity Y T (P.frequency n))
    (hR : ∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ P.frequency (n + 1) ^ (-3 : ℝ))
    (hP : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range n, (P.frequency i)⁻¹) * ‖v‖ ^ 2) :
    (ofTruncatedChildStage s hSlab hRadius hU hFlow hR hP).velocity = s.velocity := by
  subst T
  subst Λ
  rfl

@[simp] theorem ofTruncatedChildStage_pressure {P : InductiveEulerParameters} {n : ℕ}
    {activation T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity} {Y : ℝ → Velocity}
    (s : TruncatedChildStage T Λ ψ V RV)
    (hSlab : T = P.slab n activation) (hRadius : Λ = P.frequency n ^ 5)
    (hU : ∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ P.frequency n)
    (hFlow : ChildFlow.DeformationOn s.velocity Y T (P.frequency n))
    (hR : ∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ P.frequency (n + 1) ^ (-3 : ℝ))
    (hP : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range n, (P.frequency i)⁻¹) * ‖v‖ ^ 2) :
    (ofTruncatedChildStage s hSlab hRadius hU hFlow hR hP).pressure = s.pressure := by
  subst T
  subst Λ
  rfl

end InductiveEulerStage
end
end TorusEuler
