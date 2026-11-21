import TorusEuler.Paper.Proofs.S34A.Library.R42Scale
import TorusEuler.LabelFlowGeometry
import TorusEuler.LocalizedSeedRegularity

/-! Glue for the proof of **Theorem 4.2** (package S34A): the parent of Section 4 on
the normalized interval. Rescaling time by `τ = t/T` (sections/06b_mean_inverse.tex:175)
turns the parent `u` on `[0,T]` into `ũ(τ) = T u(Tτ)` on `[0,1]` with flow
`X̃(τ) = X(Tτ)`; the coefficients (4.1) become `K̃(τ) = K(Tτ)`, `Ω̃(τ) = T Ω(Tτ)`,
`M̃(τ) = T M(Tτ)` and `H̃^# = T² H^#(Tτ)`, so `H^# ≤ Id` and `T ≤ 1` give `H̃^# ≤ Id`. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

/-- The rescaled parent `ũ(τ, x) = T u(Tτ, x)`. -/
def scaledVelocity (T : ℝ) (U : Velocity) : Velocity := fun τ x => T • U (T * τ) x

/-- The rescaled two-time label flow `X̃ s τ = X (T s) (T τ)`. -/
def scaledFlow (T : ℝ) (X : ℝ → Velocity) : ℝ → Velocity := fun s τ a => X (T * s) (T * τ) a

/-- `X̃(0, τ) = X(0, Tτ)`. -/
theorem scaledFlow_zero (T : ℝ) (X : ℝ → Velocity) (τ : ℝ) :
    scaledFlow T X 0 τ = X 0 (T * τ) := by
  funext a
  simp only [scaledFlow, mul_zero]

/-- `X̃(τ, 0) = X(Tτ, 0)`, the back-to-label map of the rescaled flow. -/
theorem scaledFlow_back (T : ℝ) (X : ℝ → Velocity) (τ : ℝ) :
    scaledFlow T X τ 0 = X (T * τ) 0 := by
  funext a
  simp only [scaledFlow, mul_zero]

/-- The derivative of the time scaling `τ ↦ T τ`. -/
theorem hasDerivWithinAt_scale (T : ℝ) (s : Set ℝ) (τ : ℝ) :
    HasDerivWithinAt (fun τ : ℝ => T * τ) T s τ := by
  simpa using ((hasDerivAt_id τ).const_mul T).hasDerivWithinAt

/-- The rescaled parent is a parent of Section 4 on `[0,1]`. -/
theorem meanParentFlow_scaled {T : ℝ} {U : Velocity} {X : ℝ → Velocity}
    (hP : MeanParentFlow T U X) : MeanParentFlow 1 (scaledVelocity T U) (scaledFlow T X) := by
  have hT := hP.time_pos
  have hmap : MapsTo (fun τ : ℝ => T * τ) (Icc 0 1) (Icc 0 T) :=
    mapsTo_scale hT (mul_one T)
  have hmapS : MapsTo (fun q : ℝ × Vec3 => (T * q.1, q.2)) (Icc 0 1 ×ˢ (univ : Set Vec3))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := fun q hq => ⟨hmap hq.1, mem_univ _⟩
  have hslice (s : ℝ) (hs : s ∈ Icc 0 T) : ContDiff ℝ ∞ (U s) :=
    contDiffOn_univ.mp (hP.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨hs, mem_univ x⟩))
  refine ⟨zero_lt_one, le_rfl, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · have h := hP.smooth.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
      hmapS
    exact (contDiffOn_const (c := T)).smul h
  · intro τ hτ n x
    simp only [scaledVelocity, hP.periodic _ (hmap hτ) n x]
  · intro τ hτ x
    have hd : DifferentiableAt ℝ (U (T * τ)) x :=
      ((hslice _ (hmap hτ)).differentiable (by simp)) x
    have hfd : fderiv ℝ (scaledVelocity T U τ) x = T • fderiv ℝ (U (T * τ)) x :=
      fderiv_const_smul hd T
    have h0 := hP.divergence_free _ (hmap hτ) x
    unfold divergence at h0 ⊢
    rw [hfd]
    simp only [_root_.smul_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, h0, mul_zero]
  · intro s hs a
    exact hP.flow.initial _ (hmap hs) a
  · intro s hs a τ hτ
    have h := (hP.flow.trajectory _ (hmap hs) a _ (hmap hτ)).scomp τ
      (hasDerivWithinAt_scale T (Icc 0 1) τ) hmap
    exact h

/-- `D_a X̃(τ) = D_a X(Tτ)`. -/
theorem meanDeformation_scaled (T : ℝ) (X : ℝ → Velocity) (τ : ℝ) (a : Vec3) :
    meanDeformation (scaledFlow T X) τ a = meanDeformation X (T * τ) a := by
  simp only [meanDeformation, scaledFlow_zero]

/-- `(D_a X̃(τ))⁻¹ = (D_a X(Tτ))⁻¹`. -/
theorem meanDeformationInv_scaled (T : ℝ) (X : ℝ → Velocity) (τ : ℝ) (a : Vec3) :
    meanDeformationInv (scaledFlow T X) τ a = meanDeformationInv X (T * τ) a := by
  simp only [meanDeformationInv, scaledFlow_zero, scaledFlow_back]

/-- `K̃(τ) = K(Tτ)`. -/
theorem meanKinetic_scaled (T : ℝ) (X : ℝ → Velocity) (τ : ℝ) (a : Vec3) :
    meanKinetic (scaledFlow T X) τ a = meanKinetic X (T * τ) a := by
  simp only [meanKinetic, meanDeformation_scaled]

/-- `M̃(τ) = T M(Tτ)` on `[0,1]`. -/
theorem meanGradient_scaled {T : ℝ} {U : Velocity} {X : ℝ → Velocity}
    (hP : MeanParentFlow T U X) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (a : Vec3) :
    meanGradient (scaledVelocity T U) (scaledFlow T X) τ a = T • meanGradient U X (T * τ) a := by
  have hs : T * τ ∈ Icc 0 T := mapsTo_scale hP.time_pos (mul_one T) hτ
  have hslice : ContDiff ℝ ∞ (U (T * τ)) :=
    contDiffOn_univ.mp (hP.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨hs, mem_univ x⟩))
  simp only [meanGradient, scaledFlow_zero]
  exact fderiv_const_smul ((hslice.differentiable (by simp)) _) T

/-- `Ω̃(τ) = T Ω(Tτ)` on `[0,1]`. -/
theorem meanVorticity_scaled {T : ℝ} {U : Velocity} {X : ℝ → Velocity}
    (hP : MeanParentFlow T U X) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (a : Vec3) :
    meanVorticity (scaledVelocity T U) (scaledFlow T X) τ a =
      T • meanVorticity U X (T * τ) a := by
  simp only [meanVorticity, meanGradient_scaled hP hτ, meanDeformation_scaled, vorticityForm]
  ext w
  simp [sub_eq_add_neg, ContinuousLinearMap.comp_apply]

/-- `M̃_τ(τ) = T² M_t(Tτ)` on `[0,1]` (chain rule). -/
theorem meanGradientRate_scaled {T : ℝ} {U : Velocity} {X : ℝ → Velocity}
    (hP : MeanParentFlow T U X) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (a : Vec3) :
    meanGradientRate 1 (scaledVelocity T U) (scaledFlow T X) τ a =
      (T * T) • meanGradientRate T U X (T * τ) a := by
  have hT := hP.time_pos
  have hmap : MapsTo (fun τ : ℝ => T * τ) (Icc 0 1) (Icc 0 T) := mapsTo_scale hT (mul_one T)
  have hMsm := hP.flow.contDiffOn_materialGradient hT hP.smooth hP.periodic
  have hMtime : ContDiffOn ℝ ∞ (fun r => meanGradient U X r a) (Icc 0 T) :=
    hMsm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hr => ⟨hr, mem_univ a⟩)
  have hd : HasDerivWithinAt (fun r => meanGradient U X r a)
      (meanGradientRate T U X (T * τ) a) (Icc 0 T) (T * τ) :=
    (hMtime.differentiableOn (by simp) _ (hmap hτ)).hasDerivWithinAt
  have hcomp := (hd.scomp τ (hasDerivWithinAt_scale T (Icc 0 1) τ) hmap).const_smul T
  have hcomp' : HasDerivWithinAt (fun r => meanGradient (scaledVelocity T U) (scaledFlow T X) r a)
      (T • T • meanGradientRate T U X (T * τ) a) (Icc 0 1) τ :=
    hcomp.congr (fun r hr => meanGradient_scaled hP hr a) (meanGradient_scaled hP hτ a)
  rw [smul_smul] at hcomp'
  exact hcomp'.derivWithin (uniqueDiffOn_Icc zero_lt_one τ hτ)

/-- `H̃^#(τ) = T² H^#(Tτ)` on `[0,1]`. -/
theorem meanHsharp_scaled {T : ℝ} {U : Velocity} {X : ℝ → Velocity}
    (hP : MeanParentFlow T U X) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (a : Vec3) :
    meanHsharp 1 (scaledVelocity T U) (scaledFlow T X) τ a =
      (T * T) • meanHsharp T U X (T * τ) a := by
  simp only [meanHsharp, endpointHessian, meanGradientRate_scaled hP hτ, meanGradient_scaled hP hτ]
  ext w
  simp [smul_add, smul_smul, ContinuousLinearMap.comp_apply]

/-- The hypothesis `H^# ≤ Id` of Lemma 4.1 for the rescaled parent: `H̃^# = T² H^#` and
`T ≤ 1`. -/
theorem meanHsharp_scaled_le {T : ℝ} {U : Velocity} {X : ℝ → Velocity}
    (hP : MeanParentFlow T U X)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∀ (a w : Vec3),
      ⟪meanHsharp 1 (scaledVelocity T U) (scaledFlow T X) τ a w, w⟫_ℝ ≤ ‖w‖ ^ 2 := by
  intro τ hτ a w
  have hT := hP.time_pos
  have hT1 := hP.time_le_one
  have hs : T * τ ∈ Icc 0 T := mapsTo_scale hT (mul_one T) hτ
  rw [meanHsharp_scaled hP hτ, _root_.smul_apply, real_inner_smul_left]
  have h := hH _ hs a w
  have hw : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have hTT : T * T ≤ 1 := by nlinarith
  rcases le_total 0 ⟪meanHsharp T U X (T * τ) a w, w⟫_ℝ with h0 | h0
  · nlinarith [mul_nonneg (mul_nonneg hT.le hT.le) h0]
  · nlinarith [mul_nonneg hT.le hT.le]

end

end TorusEuler.Paper.Lib.S34A
