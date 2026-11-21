import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.S34A.Statements
import TorusEuler.ResidualGradient

/-!
# S5a library: the setting of Theorem 4.2 for the parent of §5.1

The parent of §5.1 satisfies the hypotheses of Theorem 4.2 that do not involve bounds:
it is a `MeanParentFlow` (smooth, periodic, divergence free, with its label flow, `T ≤ 1`), and
the coercivity (5.2) `D²p_U - ∇R_U ≤ Id` is the hypothesis `H^# ≤ Id` of Theorem 4.2, by
(4.3) `H^# = -(M_t + M²) = (D²p_U - ∇R_U)∘X` along each trajectory
(`endpointHessian_eq_pressureHessian_sub_residualGradient`). This is the glue every row citing
Theorem 4.2 needs (5.2, 5.4, 5.9, Aux 1.2, 1.3) to apply `Statement.theorem_4_2` to the parent.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

/-- The parent of §5.1 is a parent of Theorem 4.2 (`MeanParentFlow`). -/
theorem meanParentFlow_of_parent {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure}
    {D lam : ℝ} (hT : 0 < T) (hP : S5.Parent T U X pU D lam) : MeanParentFlow T U X :=
  ⟨hT, hP.time_le_one, hP.velocity_smooth, hP.velocity_periodic, hP.divergence_free, hP.flow⟩

/-- The coercivity (5.2) of the parent of §5.1 gives the hypothesis `H^# ≤ Id` of
Theorem 4.2, by (4.3) along each trajectory `t ↦ X(t,a)`. -/
theorem meanHsharp_le_of_parent {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure}
    {D lam : ℝ} (hT : 0 < T) (hP : S5.Parent T U X pU D lam) :
    ∀ t ∈ Icc 0 T, ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2 := by
  intro t ht a w
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.velocity_smooth.of_le (by simp)
  have hp : ContDiff ℝ ∞ (pU t) :=
    contDiffOn_univ.mp (hP.pressure_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hgrad : DifferentiableAt ℝ (gradient (pU t)) (X 0 t a) := by
    have hg : ContDiff ℝ ∞ (gradient (pU t)) := by
      have hf : ContDiff ℝ ∞ (fderiv ℝ (pU t)) := (contDiff_infty_iff_fderiv.mp hp).2
      have : gradient (pU t) = fun x => (InnerProductSpace.toDual ℝ Vec3).symm (fderiv ℝ (pU t) x) :=
        funext fun x => rfl
      rw [this]
      exact (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp hf
    exact hg.differentiable (by simp) _
  have hH := endpointHessian_eq_pressureHessian_sub_residualGradient (X := fun r => X 0 r a) hT ht
    hU₂ (hP.flow.trajectory 0 h₀ a t ht) hgrad
  have hEq : meanHsharp T U X t a =
      fderiv ℝ (gradient (pU t)) (X 0 t a) -
        fderiv ℝ (momentumResidual (Icc 0 T) U pU t) (X 0 t a) := hH
  rw [hEq]
  exact hP.coercive t ht (X 0 t a) w

end TorusEuler.Paper.Lib.S5a
