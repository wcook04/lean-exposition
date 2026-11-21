import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith

open scoped InnerProductSpace

namespace TorusEuler

/-- The pointwise pressure identity in §5.4, equation (5.16). -/
theorem transversePressureIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ V : ℝ → E} {t : ℝ} (M : E →L[ℝ] E) (f : E) (p_s : ℝ)
    (hκ : HasDerivAt κ (-(M.adjoint (κ t))) t)
    (hV : HasDerivAt V (f - M (V t) - p_s • κ t) t)
    (hperp : HasDerivAt (fun r => ⟪κ r, V r⟫_ℝ) 0 t) :
    ‖κ t‖ ^ 2 * p_s = ⟪κ t, f⟫_ℝ - 2 * ⟪κ t, M (V t)⟫_ℝ := by
  have h := (hκ.inner ℝ hV).unique hperp
  rw [inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    inner_neg_left, M.adjoint_inner_left, mul_comm p_s (‖κ t‖ ^ 2)] at h
  linarith only [h]

end TorusEuler
