import PhyslibAlpha.ClassicalMechanics.CoupledSpringPotential

/-- The coupled spring potential equals `(x₀ + x₁/2)² + (3/4) x₁²` at every point. -/
theorem couplingPotential_eq_sq_add_sq (x : EuclideanSpace ℝ (Fin 2)) :
    couplingPotential x = (x 0 + x 1 / 2) ^ 2 + 3 / 4 * (x 1) ^ 2 := by
  unfold couplingPotential
  ring

/-- The coupled spring potential is zero at the origin. -/
theorem couplingPotential_origin :
    couplingPotential (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) = 0 := by
  first
    | simp [couplingPotential]
    | norm_num [couplingPotential]

/-- At every point the coupled spring potential is at least its value at the origin. -/
theorem couplingPotential_origin_le (x : EuclideanSpace ℝ (Fin 2)) :
    couplingPotential (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) ≤ couplingPotential x := by
  rw [couplingPotential_origin, couplingPotential_eq_sq_add_sq]
  positivity

/-- Away from the origin the coupled spring potential is strictly positive. -/
theorem couplingPotential_pos (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    0 < couplingPotential x := by
  rw [couplingPotential_eq_sq_add_sq]
  by_contra h
  have hs : 0 ≤ (x 0 + x 1 / 2) ^ 2 := sq_nonneg _
  have ht : 0 ≤ (x 1) ^ 2 := sq_nonneg _
  have h1 : x 1 = 0 := by
    have h1sq : (x 1) ^ 2 = 0 := by linarith
    exact (pow_eq_zero_iff two_ne_zero).mp h1sq
  have h0 : x 0 = 0 := by
    have h0sq : (x 0 + x 1 / 2) ^ 2 = 0 := by linarith
    have h0lin : x 0 + x 1 / 2 = 0 := (pow_eq_zero_iff two_ne_zero).mp h0sq
    linarith
  apply hx
  ext i
  fin_cases i
  · first
      | simpa using h0
      | (simp; exact h0)
      | exact h0
  · first
      | simpa using h1
      | (simp; exact h1)
      | exact h1

/-- At every point other than the origin the coupled spring potential is larger than at the
origin. -/
theorem couplingPotential_origin_lt (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    couplingPotential (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) < couplingPotential x := by
  rw [couplingPotential_origin]
  exact couplingPotential_pos x hx
