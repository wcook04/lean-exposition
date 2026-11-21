import TorusEuler.Paper.Proofs.S34A.Library.R42Parent
import TorusEuler.Paper.Proofs.S34A.Library.R42Equivalence

/-! The coercivity hypothesis (A.2) of Theorem A.1 for the rescaled coefficients of
Theorem 4.2, from **Lemma 4.1** and (4.6) (sections/06b_mean_inverse.tex:178–179). -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)

/-- The coercivity constant `1/(2 D_-² (1 + ‖M‖_∞)²)` of the rescaled coefficients
`K(Tτ)`, `T Ω(Tτ)` (sections/06b_mean_inverse.tex:178–179): `h4_1` (Lemma 4.1, applied
to the rescaled parent `ũ = T u(T·)` on `[0,1]`, whose `H̃^# = T² H^# ≤ Id`) gives (4.8)
`∫ (K̃ z_τ·z_τ + Ω̃ z_τ·z) ≥ ½ ∫ |ξ_τ|²`, and (4.6) on `[0,1]`
(`integral_norm_sq_le_displacement`, with `|M̃| = T|M| ≤ ‖M‖_∞`) gives
`∫ |z_τ|² ≤ D_-²(1 + ‖M‖_∞)² ∫ |ξ_τ|²`. -/
theorem sobolevEnergy_of_hardy (h4_1 : Statement.lemma_4_1) {T : ℝ} {U : Velocity}
    {X : ℝ → Velocity} (hP : MeanParentFlow T U X)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2)
    {D L : ℝ} (hD1 : 1 ≤ D) (hDinv : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖meanDeformationInv X t a‖ ≤ D)
    (hL0 : 0 ≤ L) (hL : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖meanGradient U X t a‖ ≤ L)
    (Kt Ωt : ℝ → K½)
    (hKe : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ x, HalfHolder.eval (toUnitTorus x) (Kt τ) =
      meanKinetic X (T * τ) x)
    (hΩe : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ x, HalfHolder.eval (toUnitTorus x) (Ωt τ) =
      T • meanVorticity U X (T * τ) x) :
    EndpointSobolevEnergyBound Kt Ωt (1 / (2 * D ^ 2 * (1 + L) ^ 2)) := by
  intro a v hv
  obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
  have hT := hP.time_pos
  have hT1 := hP.time_le_one
  have hmap : MapsTo (fun τ : ℝ => T * τ) (Icc 0 1) (Icc 0 T) := mapsTo_scale hT (mul_one T)
  have hP' := meanParentFlow_scaled hP
  have hH' := meanHsharp_scaled_le hP hH
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- Lemma 4.1 for the rescaled parent: (4.8)
  have h41 := h4_1 1 _ _ hP' hH' x v hv
  obtain ⟨-, h48⟩ := h41
  -- (4.6) for the rescaled parent
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry (scaledVelocity T U))
      (Icc 0 1 ×ˢ (univ : Set Vec3)) := hP'.smooth.of_le (by simp)
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun r => meanDeformation (scaledFlow T X) r x)
        ((meanGradient (scaledVelocity T U) (scaledFlow T X) t x).comp
          (meanDeformation (scaledFlow T X) t x)) (Icc 0 1) t :=
    (hP'.flow.labelDerivative_evolves zero_lt_one hU2 hP'.periodic h01 x).2 t ht
  have hMsm := hP'.flow.contDiffOn_materialGradient zero_lt_one hP'.smooth hP'.periodic
  have cM : ContinuousOn (fun r => meanGradient (scaledVelocity T U) (scaledFlow T X) r x)
      (Icc 0 1) :=
    (hMsm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hr => ⟨hr, mem_univ x⟩)).continuousOn
  have hGF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (meanDeformationInv (scaledFlow T X) t x).comp (meanDeformation (scaledFlow T X) t x) =
        ContinuousLinearMap.id ℝ Vec3 :=
    (hP'.flow.labelDerivative_inverse zero_lt_one hU2 hP'.periodic h01 ht x).1
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖meanDeformationInv (scaledFlow T X) t x‖ ≤ D := by
    rw [meanDeformationInv_scaled]
    exact hDinv _ (hmap ht) x
  have hM (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖meanGradient (scaledVelocity T U) (scaledFlow T X) t x‖ ≤ L := by
    rw [meanGradient_scaled hP ht, norm_smul, Real.norm_of_nonneg hT.le]
    have := hL _ (hmap ht) x
    nlinarith [norm_nonneg (meanGradient U X (T * t) x)]
  have h46 := integral_norm_sq_le_displacement zero_lt_one le_rfl (by linarith) hL0 hF cM hGF hG hM
    v hv
  -- the integrand of (A.2) is that of (4.8)
  have hcongr : (∫ t in (0 : ℝ)..1,
      (⟪HalfHolder.eval (toUnitTorus x) (Kt t) (v t), v t⟫_ℝ +
        ⟪HalfHolder.eval (toUnitTorus x) (Ωt t) (v t), endpointPrimitive v t⟫_ℝ)) =
      ∫ t in (0 : ℝ)..1,
        (⟪meanKinetic (scaledFlow T X) t x (v t), v t⟫_ℝ +
          ⟪meanVorticity (scaledVelocity T U) (scaledFlow T X) t x (v t),
            endpointPrimitive v t⟫_ℝ) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro t ht
    simp only [hKe t ht x, hΩe t ht x, meanKinetic_scaled, meanVorticity_scaled hP ht]
  rw [hcongr]
  refine le_trans ?_ h48
  have hpos : 0 < 2 * D ^ 2 * (1 + L) ^ 2 := by positivity
  calc
    1 / (2 * D ^ 2 * (1 + L) ^ 2) * ‖v‖ ^ 2 ≤
        1 / (2 * D ^ 2 * (1 + L) ^ 2) * (D ^ 2 * (1 + L) ^ 2 * ∫ t in (0 : ℝ)..1,
          ‖endpointDisplacementDerivative (meanDeformation (scaledFlow T X) t x)
            (meanGradient (scaledVelocity T U) (scaledFlow T X) t x)
            (endpointPrimitive v t) (v t)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h46 (by positivity)
    _ = _ := by
      unfold endpointDisplacementDerivative
      field_simp
end

end TorusEuler.Paper.Lib.S34A
