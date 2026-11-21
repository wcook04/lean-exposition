import Breakdown.FracCell.StClauses

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

theorem isFracCert_of_clauses (h1 : ModelRegularStatement) (h2 : ModelLowerStatement) (h3 : ModelFormStatement)
    (h4 : ModelFieldStatement) (h5 : ModelPinStatement) (h6 : SplitRowsStatement) (α : ℝ) (hα₁ : 1 < α)
    (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N) (h : IsFracCell α c) : IsFracCert α (c.toCertData α) where
  order_ge := h.base.order_ge
  coercivity_pos := h.base.coercivity_pos
  coercivity_lt := h.base.coercivity_lt
  pinWeight_pos := h.base.pinWeight_pos
  rowMax_pos := h.base.rowMax_pos
  multiplierScale_pos := h.base.multiplierScale_pos
  weight_measurable := h.base.weight_measurable
  weightMin_pos := h.base.weightMin_pos
  weight_lower := h.base.weight_lower
  weight_upper := h.base.weight_upper
  weight_class := h.base.weight_class
  radius_nonneg := h.base.radius_nonneg
  slope_ne_zero := h.base.slope_ne_zero
  ellipsoidRadius_nonneg := h.base.ellipsoidRadius_nonneg
  ellipsoid_le := h.base.ellipsoid_le
  frame_near := h.base.frame_near
  frameDefect_lt := h.base.frameDefect_lt
  rotationRate_continuous := h.base.rotationRate_continuous
  multiplier_continuous := h.base.multiplier_continuous
  profile_smooth := h.base.profile_smooth
  profile_second := h.base.profile_second
  profile_divergence := h.base.profile_divergence
  profile_class := h.base.profile_class
  profile_bounds := h.base.profile_bounds
  profile_drift := h.base.profile_drift
  profile_power := h.base.profile_power
  profile_continuous := h.base.profile_continuous
  actuator_two := h.base.actuator_two
  actuator_class := h.base.actuator_class
  pin_measurable := h.base.pin_measurable
  pin_two := h.base.pin_two
  pinGap_bound := h.base.pinGap_bound
  pinGap_nonneg := h.base.pinGap_nonneg
  row_two := h.base.row_two
  row_orthonormal := h.base.row_orthonormal
  row_support := h.base.row_support
  row_class := h.base.row_class
  rowWeight_pos := h.base.rowWeight_pos
  rowWeight_le := h.base.rowWeight_le
  model_regular := h1 α hα₁ hα₂ c h
  model_lower := h2 α hα₁ hα₂ c h
  model_form := h3 α hα₁ hα₂ c h
  model_field := h4 α hα₁ hα₂ c h
  model_pin := h5 α hα₁ hα₂ c h
  losses_nonneg := h.base.losses_nonneg
  reduced_pos := h.base.reduced_pos
  reduced_le := h.base.reduced_le
  lowLoss_bound := h.base.lowLoss_bound
  reducedGap_pos := h.base.reducedGap_pos
  formScale_nonneg := h.base.formScale_nonneg
  formScale_bound := h.base.formScale_bound
  splitBound_nonneg := h.base.splitBound_nonneg
  split_rows := h6 α hα₁ hα₂ c h
  contraction_lt := h.base.contraction_lt
  productConst_nonneg := h.base.productConst_nonneg
  productConst_bound := h.base.productConst_bound
  defect_norm := h.base.defect_norm
  defect_rows := h.base.defect_rows
  size_ge := h.base.size_ge
  size_small := h.base.size_small
  adjoint_solenoidal := h.base.adjoint_solenoidal
  adjoint_local := h.base.adjoint_local
  adjoint_spread := h.base.adjoint_spread
  adjointQuad_nonneg := h.base.adjointQuad_nonneg
  adjoint_quad := h.base.adjoint_quad
  active_inclusion := h.base.active_inclusion
  stiff_inclusion := h.base.stiff_inclusion
  nontrivial := h.base.nontrivial

end CellCert

end Breakdown
