import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.CertCell.ModeHeightDerivative

open scoped ContDiff Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CertCell.SideTrace

namespace Internal.PlaneDerivs

open CellCert.CellAnalysis (cylPoint axialUnit)
open Breakdown.CertCell.Bridge.Internal.HeightOrbit Breakdown.CertCell.Bridge.Internal.HeightModes

def rotAt (q : ℝ × ℝ) (u : Space) : Space :=
  (q.1 * u 0 - q.2 * u 1) • unitVector 0 + (q.2 * u 0 + q.1 * u 1) • unitVector 1 + u 2 • unitVector 2

theorem rotAt_angle (θ : ℝ) (u : Space) : rotAt (Real.cos θ, Real.sin θ) u = axialRot θ u := rfl

theorem rotAt_smooth (u : Space) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => rotAt q u) := by
  unfold rotAt
  fun_prop

def gradEval (a b : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (frameCoord a q).comp (ContinuousLinearMap.apply ℝ Space (rotAt q (unitVector b)))

def slopeEval (a b c : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (gradEval a b q).comp (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (rotAt q (unitVector c)))

theorem gradEval_smooth (a b : Fin 3) : ContDiff ℝ ∞ (gradEval a b) :=
  (frameCoord_smooth a).clm_comp ((ContinuousLinearMap.apply ℝ Space).contDiff.comp (rotAt_smooth _))

theorem slopeEval_smooth (a b c : Fin 3) : ContDiff ℝ ∞ (slopeEval a b c) :=
  (gradEval_smooth a b).clm_comp
    ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space)).contDiff.comp (rotAt_smooth _))

theorem grad_rep (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    modeGrad ξ G 0 (planePoint p) (a, b) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg G (gradEval a b) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, b) G (gradEval a b) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, gradEval, rotAt_angle, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, frameCoord_apply]

theorem slope_rep (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) :
    modeSecondDeriv ξ H 0 (planePoint p) (a, c, b) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg H (slopeEval a b c) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, c, b) H (slopeEval a b c) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, slopeEval, gradEval, rotAt_angle,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, frameCoord_apply]

theorem mixed_rep (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    modeSecondDeriv ξ H 0 (planePoint p) (a, 2, 0) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg H (axialL (gradEval a 0)) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, 2, 0) H (axialL (gradEval a 0)) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, axialRot_third, axialL, gradEval, rotAt_angle,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, frameCoord_apply]

theorem first_weak {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hp : IsPerturbation Γ P v G H g) :
    ∀ᵐ τ, LocallyIntegrable (v τ) volume ∧
      (∀ j : Fin 3, LocallyIntegrable (fun y => G τ y (unitVector j)) volume) ∧
      ∀ φ : Space → ℝ, SteadyCert.IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) • v τ y = -∫ y, φ y • G τ y (unitVector j) := by
  filter_upwards [hp.weak_gradient] with τ hτ
  exact ⟨hτ.1, fun j => col_loc hτ.2.1 j, fun φ hφ j => by rw [hτ.2.2 φ hφ j, neg_neg]⟩

theorem second_weak {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hp : IsPerturbation Γ P v G H g) :
    ∀ᵐ τ, LocallyIntegrable (G τ) volume ∧
      (∀ j : Fin 3, LocallyIntegrable (fun y => H τ y (unitVector j)) volume) ∧
      ∀ φ : Space → ℝ, SteadyCert.IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) • G τ y = -∫ y, φ y • H τ y (unitVector j) := by
  filter_upwards [hp.weak_gradient, hp.weak_secondDeriv, hp.measurable_secondDeriv.prodMk_left] with τ h1 h2 h3
  have hH : LocallyIntegrable (H τ) volume := flip_loc h3 fun i => (h2 i).2.1
  exact ⟨h1.2.1, fun j => col_loc hH j, grad_weak_op h1.2.1 hH h2⟩

theorem rect_swap {R : Set (ℝ × ℝ)} {χ : ℝ × ℝ → ℝ} (A : ℝ × ℝ → ℂ) (hχ : ∀ p, p ∉ R → χ p = 0) :
    ∫ p in R, A p * Complex.ofReal (χ p) = ∫ p, ((χ p : ℝ) : ℂ) * A p := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by simp [hχ p hp])]
  exact integral_congr_ae (Eventually.of_forall fun p => mul_comm _ _)

theorem rect_weak {R : Set (ℝ × ℝ)} {χ ψ : ℝ × ℝ → ℝ} {A B : ℝ × ℝ → ℂ}
    (hχ : ∀ p, p ∉ R → χ p = 0) (hψ : ∀ p, p ∉ R → ψ p = 0)
    (h : ∫ p, ((χ p : ℝ) : ℂ) * A p = -∫ p, ((ψ p : ℝ) : ℂ) * B p) :
    ∫ p in R, A p * Complex.ofReal (χ p) = -∫ p in R, B p * Complex.ofReal (ψ p) := by
  rw [rect_swap A hχ, rect_swap B hψ]
  exact h

end Internal.PlaneDerivs

open Internal.PlaneDerivs Breakdown.CertCell.Bridge.Internal.HeightOrbit
  Breakdown.CertCell.Bridge.Internal.HeightModes in
theorem modePlaneDerivs (hE : Bridge.HessianEnergyIdentityHolds) : ModePlaneDerivsHolds := by
  intro Γ P v G H g hp ξ a lo hi zlo zhi hlo hlh hz
  obtain ⟨lv, lG, lH⟩ := Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hp
  have eV : planeVelocity ξ v a = fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg v (frameCoord a) ξ.1 ξ.2 p :=
    funext fun p => vel_rep ξ v a p
  have eG : ∀ b, planeGrad ξ G a b = fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg G (gradEval a b) ξ.1 ξ.2 p :=
    fun b => funext fun p => grad_rep ξ G a b p
  have eS : ∀ b c, planeSlope ξ H a b c =
      fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg H (slopeEval a b c) ξ.1 ξ.2 p :=
    fun b c => funext fun p => slope_rep ξ H a b c p
  have eGr : planeGrad ξ G a 0 =
      fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg G (radialL (frameCoord a)) ξ.1 ξ.2 p :=
    funext fun p => gradr_rep ξ G a p
  have eGz : planeGrad ξ G a 2 =
      fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg G (axialL (frameCoord a)) ξ.1 ξ.2 p :=
    funext fun p => gradz_rep ξ G a p
  have eSm : planeSlope ξ H a 0 2 =
      fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg H (axialL (gradEval a 0)) ξ.1 ξ.2 p :=
    funext fun p => mixed_rep ξ H a p
  have iV : IntegrableOn (planeVelocity ξ v a) (Icc lo hi ×ˢ Icc zlo zhi) := by
    rw [eV]
    exact (waveAvg_integrableOn v lv _ (frameCoord_smooth a).continuous _ _ hlo).const_mul _
  have iG : ∀ b, IntegrableOn (planeGrad ξ G a b) (Icc lo hi ×ˢ Icc zlo zhi) := fun b => by
    rw [eG]
    exact (waveAvg_integrableOn G lG _ (gradEval_smooth a b).continuous _ _ hlo).const_mul _
  have iS : ∀ b c, IntegrableOn (planeSlope ξ H a b c) (Icc lo hi ×ˢ Icc zlo zhi) := fun b c => by
    rw [eS]
    exact (waveAvg_integrableOn H lH _ (slopeEval_smooth a b c).continuous _ _ hlo).const_mul _
  refine ⟨⟨iV, iG 0, iG 2, iS 0 2, fun ψ hψ hc hsub => ?_⟩, fun b c => ⟨iG b, iS b c⟩⟩
  have hout : ∀ p, p ∉ Icc lo hi ×ˢ Icc zlo zhi → p ∉ tsupport ψ := fun p hp h => hp (interior_subset (hsub h))
  have hpos : ∀ p ∈ tsupport ψ, 0 < p.1 := fun p h => lt_of_lt_of_le hlo (interior_subset (hsub h)).1.1
  have z0 : ∀ p, p ∉ Icc lo hi ×ˢ Icc zlo zhi → ψ p = 0 := fun p h => image_eq_zero_of_notMem_tsupport (hout p h)
  have z1 : ∀ u : ℝ × ℝ, ∀ p, p ∉ Icc lo hi ×ˢ Icc zlo zhi → fderiv ℝ ψ p u = 0 := fun u p h => by
    have h0 : fderiv ℝ ψ p = 0 := by
      by_contra hne
      exact hout p h (support_fderiv_subset ℝ hne)
    simp [h0]
  have A := plane_weak v G lv lG (first_weak hp) (frameCoord a) (frameCoord_smooth a) ξ.1 ξ.2 ψ hψ hc hpos
  have B := plane_weak G H lG lH (second_weak hp) (gradEval a 0) (gradEval_smooth a 0) ξ.1 ξ.2 ψ hψ hc hpos
  refine ⟨rect_weak (z1 _) z0 ?_, rect_weak (z1 _) z0 ?_, rect_weak (z1 _) z0 ?_⟩
  · rw [eV, eGr]
    exact scale_id _ A.1
  · rw [eV, eGz]
    exact scale_id _ A.2
  · rw [eG 0, eSm]
    exact scale_id _ B.2

end Breakdown.CertCell.SideTrace
