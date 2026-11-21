import TorusEuler.LabelFlowGeometry
import TorusEuler.ReferenceComparison

/-! The forced variational estimate in the proof of Proposition
`cc:uf:trunc:prop:parent`, including its second-order case. -/

open ContinuousLinearMap MeasureTheory Set

namespace TorusEuler

/-- The parent variational equation has a propagator bounded by the product of
the bounds for the forward and inverse label Jacobians. A forced equation
with zero initial data therefore gains the same factor in its integral bound. -/
theorem IsLabelFlowOn.norm_forcedVariation_le
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (a : Vec3) {z N : ℝ → Vec3} {D t : ℝ}
    (hM : ContinuousOn (fun t => fderiv ℝ (U t) (X 0 t a)) (Icc 0 T))
    (hN : ContinuousOn N (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (X 0 t) a‖ ≤ D)
    (hG : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D)
    (hz₀ : z 0 = 0)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z
      (fderiv ℝ (U t) (X 0 t a) (z t) + N t) (Icc 0 T) t)
    (ht : t ∈ Icc 0 T) :
    ‖z t‖ ≤ ∫ s in (0 : ℝ)..t, D ^ 2 * ‖N s‖ := by
  let M (s : ℝ) := fderiv ℝ (U s) (X 0 s a)
  let F (s : ℝ) := fderiv ℝ (X 0 s) a
  let G (s : ℝ) := fderiv ℝ (X s 0) (X 0 s a)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hFderiv (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivWithinAt F ((M s).comp (F s)) (Icc 0 T) s :=
    (hX.labelDerivative_evolves hT hU hper h₀ a).2 s hs
  have hD : 0 ≤ D := (norm_nonneg _).trans (hF 0 h₀)
  have hStable (x : ℝ → Vec3)
      (hx : ∀ s ∈ Icc 0 T, HasDerivWithinAt x (M s (x s)) (Icc 0 T) s)
      (s : ℝ) (hs : s ∈ Icc 0 T) (u : ℝ) (hu : u ∈ Icc s T) :
      ‖x u‖ ≤ D ^ 2 * ‖x s‖ := by
    have hu' : u ∈ Icc 0 T := ⟨hs.1.trans hu.1, hu.2⟩
    let y (v : ℝ) := F v (G s (x s))
    have hy (v : ℝ) (hv : v ∈ Icc 0 T) :
        HasDerivWithinAt y (M v (y v)) (Icc 0 T) v := by
      simpa [y] using (hFderiv v hv).clm_apply
        (hasDerivWithinAt_const v (Icc 0 T) (G s (x s)))
    have hInv : (F s).comp (G s) = .id ℝ Vec3 :=
      (hX.labelDerivative_inverse hT hU hper h₀ hs a).2
    have hxy : x s = y s :=
      (congrArg (fun L : Vec3 →L[ℝ] Vec3 => L (x s)) hInv).symm
    rw [linearODE_unique_of_mem ordConnected_Icc hs hM hx hy hxy hu']
    calc
      ‖y u‖ ≤ ‖F u‖ * ‖G s (x s)‖ := (F u).le_opNorm _
      _ ≤ D * (D * ‖x s‖) := mul_le_mul (hF u hu')
        (((G s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hG s hs) (norm_nonneg _)))
        (norm_nonneg _) hD
      _ = D ^ 2 * ‖x s‖ := by ring
  simpa only [hz₀, norm_zero, mul_zero, zero_add] using
    linearODE_forced_norm_le hM hN hStable hz ht

/-- If the second label variation satisfies its differentiated ODE, the
first Jacobian and its inverse cost two powers of the parent bound in the
propagator and two more in the Hessian forcing. The Hessian bound supplies
the remaining two powers in the second-order case of the recursion. -/
theorem IsLabelFlowOn.norm_secondVariation_le
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (a u v : Vec3) {z : ℝ → Vec3} {C D t : ℝ}
    (hM : ContinuousOn (fun t => fderiv ℝ (U t) (X 0 t a)) (Icc 0 T))
    (hH : ContinuousOn (fun t => fderiv ℝ (fderiv ℝ (U t)) (X 0 t a)) (Icc 0 T))
    (hHnorm : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (fderiv ℝ (U t)) (X 0 t a)‖ ≤ C * D ^ 2)
    (hF : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (X 0 t) a‖ ≤ D)
    (hG : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D)
    (hz₀ : z 0 = 0)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z
      (fderiv ℝ (U t) (X 0 t a) (z t) +
        fderiv ℝ (fderiv ℝ (U t)) (X 0 t a) (fderiv ℝ (X 0 t) a u)
          (fderiv ℝ (X 0 t) a v)) (Icc 0 T) t)
    (ht : t ∈ Icc 0 T) :
    ‖z t‖ ≤ C * D ^ 6 * ‖u‖ * ‖v‖ := by
  let F (s : ℝ) := fderiv ℝ (X 0 s) a
  let H (s : ℝ) := fderiv ℝ (fderiv ℝ (U s)) (X 0 s a)
  let N (s : ℝ) := H s (F s u) (F s v)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hFcont : ContinuousOn F (Icc 0 T) :=
    HasDerivWithinAt.continuousOn (hX.labelDerivative_evolves hT hU hper h₀ a).2
  have hN : ContinuousOn N (Icc 0 T) :=
    (hH.clm_apply (hFcont.clm_apply continuousOn_const)).clm_apply
      (hFcont.clm_apply continuousOn_const)
  have hD : 0 ≤ D := (norm_nonneg _).trans (hF 0 h₀)
  let B := C * D ^ 6 * ‖u‖ * ‖v‖
  have hB (s : ℝ) (hs : s ∈ Icc 0 T) : D ^ 2 * ‖N s‖ ≤ B := by
    have hMu : ‖F s u‖ ≤ D * ‖u‖ :=
      ((F s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hF s hs) (norm_nonneg _))
    have hMv : ‖F s v‖ ≤ D * ‖v‖ :=
      ((F s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hF s hs) (norm_nonneg _))
    have hCH : 0 ≤ C * D ^ 2 := (norm_nonneg (H s)).trans (hHnorm s hs)
    calc
      D ^ 2 * ‖N s‖ ≤ D ^ 2 * ((‖H s‖ * ‖F s u‖) * ‖F s v‖) :=
        mul_le_mul_of_nonneg_left
          (((H s (F s u)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right ((H s).le_opNorm _) (norm_nonneg _))) (sq_nonneg _)
      _ ≤ D ^ 2 * (((C * D ^ 2) * (D * ‖u‖)) * (D * ‖v‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul (hHnorm s hs) hMu (norm_nonneg _) hCH) hMv
            (norm_nonneg _) (mul_nonneg hCH (mul_nonneg hD (norm_nonneg _)))) (sq_nonneg _)
      _ = B := by dsimp only [B]; ring
  have hB₀ : 0 ≤ B := (mul_nonneg (sq_nonneg D) (norm_nonneg (N 0))).trans (hB 0 h₀)
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hInt : IntervalIntegrable (fun s => D ^ 2 * ‖N s‖) volume 0 t :=
    (continuousOn_const.mul ((hN.mono hsub).norm)).intervalIntegrable_of_Icc ht.1
  calc
    ‖z t‖ ≤ ∫ s in (0 : ℝ)..t, D ^ 2 * ‖N s‖ :=
      hX.norm_forcedVariation_le hT hU hper a hM hN hF hG hz₀ hz ht
    _ ≤ ∫ _ in (0 : ℝ)..t, B :=
      intervalIntegral.integral_mono_on ht.1 hInt (intervalIntegrable_const) fun s hs =>
        hB s (hsub hs)
    _ = t * B := by simp [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ B := mul_le_of_le_one_left hB₀ (ht.2.trans hT₁)

end TorusEuler
