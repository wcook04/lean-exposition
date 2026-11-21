import TorusEuler.FirstWaveHierarchyInput
import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.TruncatedChildInductiveStage

/-! Closing a physical wave stage using the actual approximate fields and Fourier cutoff. -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

open MovingWaveVector (PhysicalAmplification frame entry)
open LocalizedAmplitude (CenterWaveOn)
open HierarchyTwistedProfile

noncomputable section

private theorem physicalWave_slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {u : ℝ → Vec3 → E}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (u t) :=
  contDiffOn_univ.mp (hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

namespace HierarchyTwistedProfile.PhysicalApproximationProperties

/-- Truncate the same Eulerian velocity and residual produced by the finite hierarchy. -/
theorem nonempty_cutoffStage {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {q : Pressure}
    {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
    {b : PhysicalApproximationData d q P} (h : PhysicalApproximationProperties b)
    {ψ : Vec3 → ℝ} (hEven : Function.Even ψ) (Λ : ℝ) :
    Nonempty (TruncatedChildStage T Λ ψ b.velocity b.residual) :=
  nonempty_truncatedChildStage hT (b.potential h) h.velocity_smooth h.residual_smooth
    (fun t ht => (h.periodic t ht).1) (fun t ht => (h.periodic t ht).2.2.1)
    (fun t ht => (h.reflection t ht).1) h.divergence_free h.momentum_of_potential hEven

end HierarchyTwistedProfile.PhysicalApproximationProperties

theorem ChildFlow.DeformationOn.congr_velocity {u v : Velocity} {Y : ℝ → Velocity} {T C : ℝ}
    (hY : ChildFlow.DeformationOn u Y T C)
    (hEq : ∀ t ∈ Icc 0 T, u t = v t) :
    ChildFlow.DeformationOn v Y T C := by
  refine ⟨⟨hY.flow.initial, ?_⟩, hY.lattice, hY.bounds⟩
  intro s hs x t ht
  rw [← hEq t ht]
  exact hY.flow.trajectory s hs x t ht

namespace TruncatedChildStage

open ChildFlow

/-- Smoothness and the scaled oscillatory and mean jet bounds of the
corrected profile pulled back by the parent flow. -/
structure PulledBackProfileJetBounds
    {T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity}
    (s : TruncatedChildStage T Λ ψ V RV) (X : ℝ → Velocity) (W : ℝ → Vec3 → ℝ → Vec3)
    (freq ell h B D : ℝ) (p : ℕ) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry (pullbackField X W (fun t => s.velocity t - V t)))
    (Icc 0 T ×ˢ (univ : Set PhaseState))
  oscillation : ∀ t ∈ Icc 0 T,
    PhaseJetBound 2 (B * D ^ p * freq ^ (-5 / 4 : ℝ))
      (scaledPhaseProfile ell h
        (fun x => phaseOscillation (fun r => pullbackField X W (fun t => s.velocity t - V t) t (x, r))))
  mean : ∀ t ∈ Icc 0 T,
    PhaseJetBound 1 (B * D ^ p * freq ^ (-5 / 2 : ℝ))
      (scaledPhaseProfile ell h
        (fun x _ => phaseMean (fun r => pullbackField X W (fun t => s.velocity t - V t) t (x, r))))

/-- The deformation estimate for the actual cutoff velocity, using its cutoff
tail in the pulled-back profiles. -/
theorem exists_childFlow_of_profile_jet_bounds
    {U V RV : Velocity} {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3}
    {T Λ D freq next ell h B Γ C K : ℝ} {a p b P : ℕ} {k : Vec3} {ψ : Vec3 → ℝ}
    (s : TruncatedChildStage T Λ ψ V RV) (approximatePressure : ℝ → EndpointSmoothPotential)
    (hCutoff : s.CutoffBounds approximatePressure P C K)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hDiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hP : 2 ≤ P) (hNext : freq ≤ next)
    (hErr : ∀ t ∈ Icc 0 T, K * s.truncationError P t ≤ next ^ (-5 : ℝ))
    (hVeq : ∀ t ∈ Icc 0 T, ∀ x,
      V t x = U t x + transportedProfile (fun r => X r 0) k W t x)
    (hT : 0 < T) (hT₁ : T ≤ 1)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hUdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0)
    (hX₂ : ∀ t ∈ Icc 0 T, ∀ x, ContDiffAt ℝ 2 (X 0 t) x)
    (hParent : ∀ t ∈ Icc 0 T, ∀ x : Vec3,
      ‖fderiv ℝ (X 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (X t 0) x‖ ≤ D)
    (hD : 1 ≤ D) (hfreq : 1 ≤ freq) (hell : 0 < ell) (hB : 0 ≤ B)
    (hellSize : ell⁻¹ ≤ D ^ a) (hh : h = freq ^ (-1 / 2 : ℝ))
    (hk : ‖k‖ ≤ D * freq)
    (hb : max a 1 + (max a 1 + p) + 1 ≤ b) (hΓ : 1 + 40 * B ≤ Γ)
    (hsmall : Γ * D ^ b * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hW : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (Function.uncurry (W t)))
    (hWp : ∀ t ∈ Icc 0 T, ∀ x, Function.Periodic (W t x) 1)
    (hWskew : ∀ t ∈ Icc 0 T, ∀ (n : Fin 3 → ℤ) x r,
      W t (x + latticeVector n) (r + ⟪k, latticeVector n⟫_ℝ) = W t x r)
    (hWdiv : ∀ t ∈ Icc 0 T, ∀ x r,
      divergence (fun y => W t (X t 0 y) r) (X 0 t x) +
        ⟪(fderiv ℝ (X t 0) (X 0 t x)).adjoint k, deriv (W t x) r⟫_ℝ = 0)
    (hJets : PulledBackProfileJetBounds s X W freq ell h B D p) :
    ∃ Y : ℝ → Velocity, DeformationOn s.velocity Y T (Γ * D ^ b * freq ^ (1 / 4 : ℝ)) := by
  let v : Velocity := fun t => s.velocity t - V t
  obtain ⟨_, hTail⟩ := s.cutoffTail_for_childFlow approximatePressure hCutoff hV hDiv hP hfreq hNext hErr
  have hvper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (v t) :=
    (hTail t ht).1
  have hvdiv (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      DifferentiableAt ℝ (v t) x ∧ divergence (v t) x = 0 :=
    ⟨((hTail t ht).2.2.1.1.differentiable (by norm_num)) x, (hTail t ht).2.1 x⟩
  obtain ⟨Y, hY⟩ := ChildFlow.exists_childFlow_of_profile_jet_bounds (v := v)
    hT hT₁ hX hU hper hUdiv hX₂ hParent hD hfreq hell hB hellSize hh hk hb hΓ hsmall
    hJets.smooth hW hWp hWskew hWdiv hvper hvdiv hJets.oscillation hJets.mean
  refine ⟨Y, hY.congr_velocity (fun t ht => funext fun x => ?_)⟩
  change U t x + transportedProfile (fun r => X r 0) k W t x +
    (s.velocity t x - V t x) = s.velocity t x
  rw [← hVeq t ht x]
  abel

end TruncatedChildStage

namespace ChildFlow

/-- The perturbation pulled back by the actual parent flow is jointly smooth. -/
theorem contDiffOn_pullbackField_of_parent
    {T : ℝ} {U v : Velocity} {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3}
    (hT : 0 < T) (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hW : ContDiffOn ℝ ∞ (Function.uncurry fun t => Function.uncurry (W t))
      (Icc 0 T ×ˢ (univ : Set PhaseState)))
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (Function.uncurry (pullbackField X W v))
      (Icc 0 T ×ˢ (univ : Set PhaseState)) := by
  let sliceLabel (z : ℝ × PhaseState) : ℝ × Vec3 := (z.1, z.2.1)
  have hLabel : ContDiff ℝ ∞ sliceLabel :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hMapsLabel : MapsTo sliceLabel (Icc 0 T ×ˢ (univ : Set PhaseState))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := fun z hz => ⟨hz.1, mem_univ _⟩
  have hF := (hX.contDiffOn_forwardLabelFlow hT hU hper).comp hLabel.contDiffOn hMapsLabel
  have hG := (hX.contDiffOn_inverseLabelDerivative hT hU hper).comp hLabel.contDiffOn hMapsLabel
  have hTail := hv.comp (contDiffOn_fst.prodMk hF) (fun z hz => ⟨hz.1, mem_univ _⟩)
  exact hG.clm_apply (hW.add hTail)

/-- The cutoff tail shifts the phase mean by its label-dependent pullback. -/
theorem phaseMean_pullbackField_eq_add
    {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3} {v : Velocity} {t : ℝ} {x : Vec3}
    (hW : Continuous (W t x)) :
    phaseMean (fun r => pullbackField X W v t (x, r)) =
      phaseMean (fun r => pullbackField X W 0 t (x, r)) +
        (fderiv ℝ (X t 0) (X 0 t x)) (v t (X 0 t x)) := by
  let G := fderiv ℝ (X t 0) (X 0 t x)
  have heq : (fun r => pullbackField X W v t (x, r)) =
      fun r => G (W t x r) + G (v t (X 0 t x)) :=
    funext fun r => map_add G _ _
  have hf : Continuous (fun r => G (W t x r)) := (ContinuousLinearMap.continuous G).comp hW
  have hc : Continuous (fun _ : ℝ => G (v t (X 0 t x))) := continuous_const
  rw [heq, phaseMean_add hf hc, phaseMean_const]
  simp [pullbackField, G]

/-- The phase-independent cutoff tail contributes no oscillatory term. -/
theorem phaseOscillation_pullbackField_eq_uncut
    {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3} {v : Velocity} {t : ℝ} {x : Vec3}
    (hW : Continuous (W t x)) :
    phaseOscillation (fun r => pullbackField X W v t (x, r)) =
      phaseOscillation (fun r => pullbackField X W 0 t (x, r)) := by
  funext r
  unfold phaseOscillation
  rw [phaseMean_pullbackField_eq_add hW]
  have heq : pullbackField X W v t (x, r) = pullbackField X W 0 t (x, r) +
      (fderiv ℝ (X t 0) (X 0 t x)) (v t (X 0 t x)) := by
    simp only [pullbackField, map_add, Pi.zero_apply, add_zero]
  simp only [heq]
  abel

end ChildFlow

open ContinuousLinearMap Set
open scoped ContDiff

namespace ChildFlow

/-- A phase-independent perturbation costs at most one derivative of the inverse
deformation and one derivative of the forward map. -/
theorem scaledPerturbation_phaseJetBound_one
    {A v : Vec3 → Vec3} {G : Vec3 → Vec3 →L[ℝ] Vec3}
    {ell h A₁ G₀ G₁ ε : ℝ}
    (hell : |ell| ≤ 1) (hA : Differentiable ℝ A) (hG : Differentiable ℝ G)
    (hA₁ : ∀ a, ‖fderiv ℝ A a‖ ≤ A₁) (hG₀ : ∀ a, ‖G a‖ ≤ G₀)
    (hG₁ : ∀ a, ‖fderiv ℝ G a‖ ≤ G₁)
    (hdv : Differentiable ℝ v) (hv₀ : ∀ a, ‖v a‖ ≤ ε) (hv₁ : ∀ a, ‖fderiv ℝ v a‖ ≤ ε) :
    PhaseJetBound 1 (max G₀ (G₀ * A₁ + G₁) * ε)
      (scaledPhaseProfile ell h (fun a _ => G a (v (A a)))) := by
  have hε₀ : 0 ≤ ε := (norm_nonneg _).trans (hv₀ 0)
  have hA₁₀ : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hG₀₀ : 0 ≤ G₀ := (norm_nonneg _).trans (hG₀ 0)
  let F (a : Vec3) := G a (v (A a))
  let L := ell • ContinuousLinearMap.fst ℝ Vec3 ℝ
  have hProfile : scaledPhaseProfile ell h (fun a _ => G a (v (A a))) = F ∘ L := rfl
  have hL : ‖L‖ ≤ 1 := by
    change ‖ell • ContinuousLinearMap.fst ℝ Vec3 ℝ‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg ell) (ContinuousLinearMap.norm_fst_le _ _ _)).trans hell
  have hF₀ (a : Vec3) : ‖F a‖ ≤ G₀ * ε :=
    ((G a).le_opNorm _).trans (mul_le_mul (hG₀ a) (hv₀ _) (norm_nonneg _) hG₀₀)
  have hDeriv (a : Vec3) : HasFDerivAt F
      ((G a).comp ((fderiv ℝ v (A a)).comp (fderiv ℝ A a)) +
        (fderiv ℝ G a).flip (v (A a))) a :=
    (hG a).hasFDerivAt.clm_apply ((hdv (A a)).hasFDerivAt.comp a (hA a).hasFDerivAt)
  have hF₁ (a : Vec3) : ‖fderiv ℝ F a‖ ≤ (G₀ * A₁ + G₁) * ε := by
    rw [(hDeriv a).fderiv]
    refine (norm_add_le _ _).trans ?_
    have hComp : ‖(G a).comp ((fderiv ℝ v (A a)).comp (fderiv ℝ A a))‖ ≤
        G₀ * (ε * A₁) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hG₀ a) ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hv₁ _) (hA₁ a) (norm_nonneg _) hε₀)) (norm_nonneg _) hG₀₀)
    have hFlip : ‖(fderiv ℝ G a).flip (v (A a))‖ ≤ G₁ * ε := by
      exact ((by simpa only [ContinuousLinearMap.opNorm_flip] using
        (fderiv ℝ G a).flip.le_opNorm (v (A a))) :
        ‖(fderiv ℝ G a).flip (v (A a))‖ ≤ ‖fderiv ℝ G a‖ * ‖v (A a)‖).trans
          (mul_le_mul (hG₁ a) (hv₀ _) (norm_nonneg _) ((norm_nonneg (fderiv ℝ G a)).trans (hG₁ a)))
    calc
      _ ≤ G₀ * (ε * A₁) + G₁ * ε := add_le_add hComp hFlip
      _ = _ := by ring
  rw [hProfile]
  intro j hj z
  interval_cases j
  · rw [norm_iteratedFDeriv_zero]
    exact (hF₀ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε₀)
  · rw [norm_iteratedFDeriv_one, ((hDeriv (L z)).comp z L.hasFDerivAt).fderiv,
      ← (hDeriv (L z)).fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hL).trans
        ((hF₁ _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε₀)))

/-- The phase-independent tail costs at most one derivative of the inverse
deformation and one derivative of the forward map. -/
theorem scaledCutoffTail_phaseJetBound_one
    {A v : Vec3 → Vec3} {G : Vec3 → Vec3 →L[ℝ] Vec3}
    {ell h A₁ G₀ G₁ ε : ℝ}
    (hell : |ell| ≤ 1) (hA : Differentiable ℝ A) (hG : Differentiable ℝ G)
    (hA₁ : ∀ a, ‖fderiv ℝ A a‖ ≤ A₁) (hG₀ : ∀ a, ‖G a‖ ≤ G₀)
    (hG₁ : ∀ a, ‖fderiv ℝ G a‖ ≤ G₁)
    (hv : SpatialHolderHalf 2 v) (hε : spatialHolderHalfNorm 2 v ≤ ε) :
    PhaseJetBound 1 (max G₀ (G₀ * A₁ + G₁) * ε)
      (scaledPhaseProfile ell h (fun a _ => G a (v (A a)))) := by
  refine scaledPerturbation_phaseJetBound_one hell hA hG hA₁ hG₀ hG₁
    (hv.1.differentiable (by norm_num)) ?_ ?_
  · intro a
    simpa only [norm_iteratedFDeriv_zero] using
      (norm_iteratedFDeriv_le_spatialHolderHalfNorm hv (by decide : 0 ≤ 2) a).trans hε
  · intro a
    simpa only [norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_le_spatialHolderHalfNorm hv (by decide : 1 ≤ 2) a).trans hε

end ChildFlow

namespace TruncatedChildStage

open Set ChildFlow
open scoped ContDiff

private theorem pullback_slice_smooth {T : ℝ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ → E → F}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (u t) :=
  contDiffOn_univ.mp (hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- Add two first-order bounds for differentiable profiles. -/
theorem phaseJetBound_one_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → Vec3} {C D : ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hF : PhaseJetBound 1 C f) (hG : PhaseJetBound 1 D g) :
    PhaseJetBound 1 (C + D) (f + g) := by
  intro j hj x
  interval_cases j
  · simp only [norm_iteratedFDeriv_zero, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add
      (by simpa only [norm_iteratedFDeriv_zero] using hF 0 (by decide) x)
      (by simpa only [norm_iteratedFDeriv_zero] using hG 0 (by decide) x))
  · rw [norm_iteratedFDeriv_one, fderiv_add (hf x) (hg x)]
    exact (norm_add_le _ _).trans (add_le_add
      (by simpa only [norm_iteratedFDeriv_one] using hF 1 le_rfl x)
      (by simpa only [norm_iteratedFDeriv_one] using hG 1 le_rfl x))

/-- Build the corrected pulled-back jet estimates from the uncut hierarchy.
The cutoff tail enters only the mean and its cost is controlled by the
first derivative of the inverse deformation along the parent flow. -/
theorem PulledBackProfileJetBounds.of_uncut
    {T Λ freq ell h B D D₁ M ε C K : ℝ} {p P : ℕ}
    {ψ : Vec3 → ℝ} {U V RV : Velocity} {X : ℝ → Velocity}
    {W : ℝ → Vec3 → ℝ → Vec3}
    (s : TruncatedChildStage T Λ ψ V RV)
    {approximatePressure : ℝ → EndpointSmoothPotential}
    (hCutoff : s.CutoffBounds approximatePressure P C K) (hP : 2 ≤ P)
    (hT : 0 < T) (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hW : ContDiffOn ℝ ∞ (Function.uncurry fun t => Function.uncurry (W t))
      (Icc 0 T ×ˢ (univ : Set PhaseState)))
    (hell : |ell| ≤ 1)
    (hParent : ∀ t ∈ Icc 0 T, ∀ x : Vec3,
      ‖fderiv ℝ (X 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (X t 0) x‖ ≤ D)
    (hD₁ : ∀ t ∈ Icc 0 T, ∀ a : Vec3,
      ‖fderiv ℝ (fun x => fderiv ℝ (X t 0) (X 0 t x)) a‖ ≤ D₁)
    (hSize : ∀ t ∈ Icc 0 T, K * s.truncationError P t ≤ ε)
    (hosc : ∀ t ∈ Icc 0 T, PhaseJetBound 2 (B * D ^ p * freq ^ (-5 / 4 : ℝ))
      (scaledPhaseProfile ell h (fun x => phaseOscillation
        (fun r => pullbackField X W 0 t (x, r)))))
    (hmean : ∀ t ∈ Icc 0 T, PhaseJetBound 1 M
      (scaledPhaseProfile ell h (fun x _ => phaseMean (fun r => pullbackField X W 0 t (x, r)))))
    (hBudget : M + max D (D * D + D₁) * ε ≤ B * D ^ p * freq ^ (-5 / 2 : ℝ)) :
    PulledBackProfileJetBounds s X W freq ell h B D p := by
  let v : Velocity := fun t => s.velocity t - V t
  have hs : ContDiffOn ℝ ∞ (Function.uncurry s.velocity) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    s.smooth_velocity
  have hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hs.sub hV
  have hUncut := contDiffOn_pullbackField_of_parent hT hX hU hper hW
    (v := (0 : Velocity)) contDiffOn_const
  have hWphase (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) : Continuous (W t x) :=
    ((pullback_slice_smooth hW ht).comp (contDiff_const.prodMk contDiff_id)).continuous
  refine ⟨contDiffOn_pullbackField_of_parent hT hX hU hper hW hv, ?_, ?_⟩
  · intro t ht
    have eqOsc : (fun x => phaseOscillation (fun r => pullbackField X W v t (x, r))) =
        fun x => phaseOscillation (fun r => pullbackField X W 0 t (x, r)) :=
      funext fun x => phaseOscillation_pullbackField_eq_uncut (hWphase t ht x)
    change PhaseJetBound 2 _ (scaledPhaseProfile ell h (fun x =>
      phaseOscillation (fun r => pullbackField X W v t (x, r))))
    rw [eqOsc]
    exact hosc t ht
  · intro t ht
    let A := X 0 t
    let G (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
    let f (x : Vec3) (r : ℝ) := pullbackField X W 0 t (x, r)
    let mean : PhaseState → Vec3 := scaledPhaseProfile ell h (fun x _ => phaseMean (f x))
    let tail : PhaseState → Vec3 := scaledPhaseProfile ell h (fun x _ => G x (v t (A x)))
    let L : PhaseState →L[ℝ] Vec3 := ell • ContinuousLinearMap.fst ℝ Vec3 ℝ
    have hA : ContDiff ℝ ∞ A :=
      pullback_slice_smooth (hX.contDiffOn_forwardLabelFlow hT hU hper) ht
    have hGjoint : ContDiffOn ℝ ∞ (Function.uncurry
        (fun t x => fderiv ℝ (X t 0) (X 0 t x))) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      hX.contDiffOn_inverseLabelDerivative hT hU hper
    have hG : ContDiff ℝ ∞ G := pullback_slice_smooth hGjoint ht
    have hf : ContDiff ℝ ∞ (Function.uncurry f) := pullback_slice_smooth hUncut ht
    have hfMean : ContDiff ℝ ∞ (fun x => phaseMean (f x)) :=
      contDiffOn_univ.mp (contDiffOn_phaseMean (f := f) convex_univ uniqueDiffOn_univ hf.contDiffOn)
    have hMeanDiff : Differentiable ℝ mean :=
      (hfMean.comp L.contDiff).differentiable (by simp)
    have hTailSmooth : ContDiff ℝ ∞ tail :=
      (hG.clm_apply ((pullback_slice_smooth hv ht).comp hA)).comp L.contDiff
    have hTailDiff := hTailSmooth.differentiable (by simp)
    have hTailJet : PhaseJetBound 1 (max D (D * D + D₁) * ε) tail :=
      scaledCutoffTail_phaseJetBound_one hell (hA.differentiable (by simp))
        (hG.differentiable (by simp)) (fun x => (hParent t ht x).1)
        (fun x => (hParent t ht (A x)).2) (hD₁ t ht)
        (hCutoff.all_tails 2 hP t ht).1 ((hCutoff.tail_two t ht).trans (hSize t ht))
    have eqMean : scaledPhaseProfile ell h (fun x _ => phaseMean
        (fun r => pullbackField X W v t (x, r))) = mean + tail := by
      funext z
      exact phaseMean_pullbackField_eq_add (hWphase t ht (L z))
    change PhaseJetBound 1 _ (scaledPhaseProfile ell h (fun x _ =>
      phaseMean (fun r => pullbackField X W v t (x, r))))
    rw [eqMean]
    intro j hj z
    exact (phaseJetBound_one_add hMeanDiff hTailDiff (hmean t ht) hTailJet j hj z).trans hBudget

end TruncatedChildStage

namespace InductiveEulerWave

private theorem growingCutoffCenter
    {I : Set ℝ} {t₀ μ T scale Ustar ratio half : ℝ}
    {w : PhysicalAmplification I t₀} {b q qNext : ℕ}
    {parent V child tail : Velocity} {E : ℝ → Vec3 →L[ℝ] Vec3}
    (d : w.GrowingCrossing T scale Ustar ratio)
    (hScale : scale = μ ^ frequencyExponent b q)
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hhalf : d.crossing - t₀ ≤ half)
    (hChild : ∀ r ∈ w.activeSlab T, child r = V r + tail r)
    (hV : ∀ r ∈ w.activeSlab T, DifferentiableAt ℝ (V r) 0)
    (hTail : ∀ r ∈ w.activeSlab T, SpatialHolderHalf 2 (tail r) ∧
      spatialHolderHalfNorm 2 (tail r) ≤ (scale ^ frequencyExponent b qNext) ^ (-5 : ℝ))
    (hPre : ∀ r ∈ w.activeSlab T,
      fderiv ℝ (V r) 0 = fderiv ℝ (parent r) 0 +
        waveSwitch t₀ w.rate r • InnerProductSpace.rankOne ℝ (d.amplitude r) (d.waveVector r) + E r ∧
      ‖E r‖ ≤ scale ^ (-1 / 3 : ℝ)) :
    ∀ r ∈ w.activeSlab T,
      fderiv ℝ (child r) 0 = fderiv ℝ (parent r) 0 +
        waveSwitch t₀ w.rate r • InnerProductSpace.rankOne ℝ (d.amplitude r) (d.waveVector r) +
        (E r + fderiv ℝ (tail r) 0) ∧
      ‖E r + fderiv ℝ (tail r) 0‖ ≤ scale ^ (-1 / 4 : ℝ) := by
  subst scale
  exact (frequencySchedule_child_T4_center d hμ hb hhalf hChild hV hTail hPre).1

/-- The actual cutoff correction adds its spatial first jet to the central error
of the approximate velocity. The normalized crossing fixes the cutoff and ratio
of this same wave. -/
def ofGrowingCrossingCutoff
    {P : InductiveEulerParameters} {n depth : ℕ} {tOld t window Λ C K : ℝ}
    {ψ : Vec3 → ℝ} {V RV osc : Velocity} {rawError : ℝ → Vec3 →L[ℝ] Vec3}
    {w : PhysicalAmplification (Icc t (P.slab (n + 1) t)) t}
    (parent : InductiveEulerStage P n tOld) (child : InductiveEulerStage P (n + 1) t)
    (s : TruncatedChildStage (P.slab (n + 1) t) Λ ψ V RV)
    (hChild : child.velocity = s.velocity)
    (d : w.GrowingCrossing window (P.frequency (n + 1))
      (P.frequency (n + 1) ^ (-3 / 4 : ℝ))
      (couplingRatioOfGain (4 * Real.log (P.frequency (n + 3)))))
    (hμ : 2 ≤ P.frequency n) (ht : 0 ≤ t)
    (hSlab : w.clock window = P.slab (n + 1) t)
    (hHalf : d.crossing - t ≤ inductionHalfLength P.frequency n)
    (hGradient : EqOn w.gradient (fun r => fderiv ℝ (parent.velocity r) 0)
      (Icc t (P.slab (n + 1) t)))
    (hCenter : CenterWaveOn (fun r => fderiv ℝ (parent.velocity r) 0) d.waveVector d.amplitude t
      (P.slab (n + 1) t) (P.frequency n ^ 9))
    (hOsc : ∀ r ∈ Icc 0 (P.slab (n + 1) t), ∀ x, ‖osc r x‖ ≤ (P.frequency (n + 1))⁻¹)
    (hCorrection : ∀ m ≤ P.order (n + 1), ∀ r ∈ Icc 0 (P.slab (n + 1) t),
      let v := s.velocity r - parent.velocity r - osc r
      SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (P.frequency (n + 1))⁻¹)
    (hVanish : 2 ≤ n + 1 → ∀ r ∈ Icc 0 t, osc r = 0)
    (hSupport : ∀ r ∈ Icc 0 (P.slab (n + 1) t), ∀ x, osc r x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency n)⁻¹)
    (approximatePressure : ℝ → EndpointSmoothPotential)
    (hCut : s.CutoffBounds approximatePressure depth C K) (hDepth : 2 ≤ depth)
    (hTail : ∀ r ∈ Icc 0 (P.slab (n + 1) t),
      K * s.truncationError depth r ≤ P.frequency (n + 2) ^ (-5 : ℝ))
    (hVSmooth : ContDiffOn ℝ ∞ (Function.uncurry V)
      (Icc 0 (P.slab (n + 1) t) ×ˢ (univ : Set Vec3)))
    (hApprox : ∀ r ∈ Icc t (P.slab (n + 1) t),
      fderiv ℝ (V r) 0 = fderiv ℝ (parent.velocity r) 0 +
        waveSwitch t w.rate r • InnerProductSpace.rankOne ℝ (d.amplitude r) (d.waveVector r) +
        rawError r ∧ ‖rawError r‖ ≤ P.frequency (n + 1) ^ (-1 / 3 : ℝ))
    (hStrength :
      P.strengthConstant⁻¹ * P.frequency (n + 1) ^ (1 / 4 : ℝ) ≤
        ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ∧
      ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ≤
        P.strengthConstant * P.frequency (n + 1) ^ (1 / 4 : ℝ) *
          (4 * Real.log (P.frequency (n + 3))) ^ 2)
    (hCoupling : Real.pi ≤ w.physicalNu d.waveVector d.amplitude d.crossing ∧
      w.physicalNu d.waveVector d.amplitude d.crossing ≤ 4 * Real.pi) :
    InductiveEulerWave P n parent child d.crossing := by
  let tail : Velocity := fun r => s.velocity r - V r
  have hActive : w.activeSlab window = Icc t (P.slab (n + 1) t) := by
    unfold PhysicalAmplification.activeSlab
    rw [hSlab]
  have hFull {r : ℝ} (hr : r ∈ w.activeSlab window) : r ∈ Icc 0 (P.slab (n + 1) t) := by
    rw [hActive] at hr
    exact ⟨ht.trans hr.1, hr.2⟩
  have hVSlice (r : ℝ) (hr : r ∈ w.activeSlab window) : DifferentiableAt ℝ (V r) 0 := by
    have hs := hVSmooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x (_ : x ∈ (univ : Set Vec3)) => mem_prod.mpr ⟨hFull hr, mem_univ x⟩)
    exact ((contDiffOn_univ.mp hs).differentiable (by simp)) 0
  have hChildSplit (r : ℝ) (_ : r ∈ w.activeSlab window) : child.velocity r = V r + tail r := by
    rw [hChild]
    dsimp only [tail]
    abel
  have hc := growingCutoffCenter
    (b := P.exponentParameter) (q := P.order (n + 1)) (qNext := P.order (n + 2))
    (E := rawError) (parent := parent.velocity)
    d (P.frequency_step n) hμ P.exponentParameter_ge hHalf hChildSplit hVSlice
    (fun r hr => ⟨(hCut.all_tails 2 hDepth r (hFull hr)).1,
      (hCut.tail_two r (hFull hr)).trans (by
        rw [← P.frequency_step (n + 1)]
        exact hTail r (hFull hr))⟩)
    (fun r hr => hApprox r (hActive ▸ hr))
  let E := fun r => rawError r + fderiv ℝ (tail r) 0
  refine
    { oscillation := osc
      waveVector := d.waveVector
      amplitude := d.amplitude
      cutoff := waveSwitch t w.rate
      error := E
      center := hCenter
      activation_step := ?_
      oscillation_bound := hOsc
      correction_bound := by simpa only [hChild] using hCorrection
      oscillation_vanishes := hVanish
      oscillation_support := hSupport
      gradient_split := ?_
      error_bound := ?_
      cutoff_complete := ?_
      strength_at_crossing := hStrength
      coupling_at_crossing := ?_
      ratio_at_crossing := ?_ }
  · exact ⟨sub_nonneg.mpr d.crossing_in_slab.1, hHalf⟩
  · intro r hr
    have h := (hc r (hActive.symm ▸ hr)).1
    simpa only [InnerProductSpace.rankOne_def] using h
  · intro r hr
    exact (hc r (hActive.symm ▸ hr)).2
  · exact fun r hr => d.waveSwitch_eq_one_after hr.1
  · have hAt := hGradient (hActive ▸ d.crossing_in_slab)
    simp only [PhysicalAmplification.physicalNu, hAt] at hCoupling
    exact hCoupling
  · have hAt := hGradient (hActive ▸ d.crossing_in_slab)
    have hRatio := d.crossing_ratio
    simp only [PhysicalAmplification.physicalNu, PhysicalAmplification.physicalEta, hAt] at hRatio
    exact hRatio

/-- The scheduled logarithmic gain and the common strength constant give the
crossing strength of the selected physical pair. -/
theorem growingCrossingStrength
    {P : InductiveEulerParameters} {n : ℕ} {t window peak : ℝ}
    {w : PhysicalAmplification (Icc t (P.slab (n + 1) t)) t}
    (d : w.GrowingCrossing window (P.frequency (n + 1)) peak
      (couplingRatioOfGain (4 * Real.log (P.frequency (n + 3)))))
    (hPeak : peak = P.frequency (n + 1) ^ (-3 / 4 : ℝ))
    (hLarge : Real.exp 4 ≤ P.frequency 0)
    (hConst : 18 * Real.exp 3 ≤ P.strengthConstant)
    (hRatio : w.ratio = couplingRatioOfGain (4 * Real.log (P.frequency (n + 2)))) :
    P.strengthConstant⁻¹ * P.frequency (n + 1) ^ (1 / 4 : ℝ) ≤
      ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ∧
    ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ≤
      P.strengthConstant * P.frequency (n + 1) ^ (1 / 4 : ℝ) *
        (4 * Real.log (P.frequency (n + 3))) ^ 2 := by
  have hBase : 1 < P.frequency 0 := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hLarge
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hBase.le P.frequency_step
  have hPos (i : ℕ) : 1 < P.frequency i := hBase.trans_le (hMono (Nat.zero_le i))
  have hL : 1 ≤ 4 * Real.log (P.frequency (n + 2)) := by
    have h := Real.log_le_log (Real.exp_pos 4) (hLarge.trans (hMono (Nat.zero_le (n + 2))))
    rw [Real.log_exp] at h
    linarith
  have hStep := (frequencySchedule_gain_ratio P.exponentParameter P.order P.frequency
    (fun i => 4 * Real.log (P.frequency (i + 1))) (n + 1) P.exponentParameter_ge
    (P.order_maximum (n + 1)).1.1 (hPos (n + 2)) (P.frequency_step (n + 2))
    (fun _ => rfl)).2
  have hScale : 0 < P.frequency (n + 1) := zero_lt_one.trans (hPos _)
  rw [show (-3 / 4 : ℝ) = -(3 / 4) by ring] at hPeak
  subst peak
  have hB := d.strength_bounds_for_next hScale hL hStep hRatio
  have hLower : P.strengthConstant⁻¹ ≤ Real.exp (-1) / 4 :=
    ((inv_le_inv₀ (zero_lt_two.trans_le P.strengthConstant_ge) (by positivity)).2 hConst).trans
      inductionCrossingStrengthConstants.2
  constructor
  · exact (mul_le_mul_of_nonneg_right hLower (Real.rpow_nonneg hScale.le _)).trans hB.1
  · exact hB.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hConst (Real.rpow_nonneg hScale.le _)) (sq_nonneg _))

end InductiveEulerWave

namespace InductiveEulerBase

/-- Assemble the stationary base and the actual truncated first wave.
The physical first wave has the constant-one cutoff and both activations are zero. -/
def ofFirstWaveCutoff
    {P : InductiveEulerParameters} {depth : ℕ} {tilt r h Λ C K Cstep : ℝ}
    {ψ : Vec3 → ℝ} {V RV osc oscRemainder mean : Velocity}
    (parent : InductiveEulerStage P 0 0) (child : InductiveEulerStage P 1 0)
    (s : TruncatedChildStage (P.slab 1 0) Λ ψ V RV)
    (hChild : child.velocity = s.velocity)
    (w : FirstWaveOrigin tilt (P.slab 1 0) (P.frequency 1))
    (hLife : P.LifetimeBounds) (hμ : 2 ≤ P.frequency 0)
    (hTilt : tilt = couplingRatioOfGain (4 * Real.log (P.frequency 3)))
    (hTiltSmall : |tilt| ≤ 1) (hL : 1 ≤ 4 * Real.log (P.frequency 3))
    (hParent : parent.velocity = fun _ => stationaryShear tilt)
    (hr : 0 < r) (hCell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hSmall : P.slab 1 0 * ‖stationaryShearGradient tilt‖ ≤ 1 / 8)
    (hCstep : Cstep ≤ P.frequency 1 ^ (1 / 32 : ℝ))
    (hOscillation : ∀ τ ∈ Icc 0 (P.slab 1 0), ∀ x, ‖osc τ x‖ ≤ (P.frequency 1)⁻¹)
    (hCorrection : ∀ m ≤ P.order 1, ∀ τ ∈ Icc 0 (P.slab 1 0),
      let v := s.velocity τ - parent.velocity τ - osc τ
      SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (P.frequency 1)⁻¹)
    (hSupport : ∀ τ ∈ Icc 0 (P.slab 1 0), ∀ x, osc τ x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency 0)⁻¹)
    (approximatePressure : ℝ → EndpointSmoothPotential)
    (hCut : s.CutoffBounds approximatePressure depth C K) (hDepth : 2 ≤ depth)
    (hTail : ∀ τ ∈ Icc 0 (P.slab 1 0), K * s.truncationError depth τ ≤ P.frequency 2 ^ (-5 : ℝ))
    (hV : ∀ τ ∈ Icc 0 (P.slab 1 0), V τ = stationaryShear tilt +
      localizedTransportedProfile (fun u => stationaryShearFlow tilt (-u))
        (P.frequency 1 • EuclideanSpace.single 0 1) (firstWaveLeadingProfile tilt w.scale r h) τ +
      oscRemainder τ + mean τ)
    (hOsc : ∀ τ ∈ Icc 0 (P.slab 1 0), DifferentiableAt ℝ (oscRemainder τ) 0)
    (hMean : ∀ τ ∈ Icc 0 (P.slab 1 0), DifferentiableAt ℝ (mean τ) 0)
    (hRem : ∀ τ ∈ Icc 0 (P.slab 1 0), ‖fderiv ℝ (oscRemainder τ) 0‖ + ‖fderiv ℝ (mean τ) 0‖ ≤
      Cstep * P.frequency 1 ^ (-5 / 12 : ℝ)) :
    InductiveEulerBase P := by
  let tail : Velocity := fun τ => s.velocity τ - V τ
  let E := fun τ => fderiv ℝ (oscRemainder τ) 0 + fderiv ℝ (mean τ) 0 + fderiv ℝ (tail τ) 0
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (one_le_two.trans hμ) P.frequency_step
  have hExponent : 12 ≤ frequencyExponent P.exponentParameter (P.order 1) := by
    rw [P.initial_order]
    unfold frequencyExponent
    have h := Nat.mul_le_mul_left 320 P.exponentParameter_ge
    omega
  have hFreq : (2 : ℝ) ^ (12 : ℕ) ≤ P.frequency 1 := by
    rw [P.frequency_step 0]
    exact (pow_le_pow_left₀ zero_le_two hμ _).trans
      (pow_le_pow_right₀ (one_le_two.trans hμ) hExponent)
  have hFpos : 0 < P.frequency 1 := (zero_lt_two.trans_le hμ).trans_le (hMono (by decide))
  have hD : 2 ≤ P.frequency 0 ^ (9 : ℕ) :=
    hμ.trans (le_self_pow₀ (one_le_two.trans hμ) (by decide))
  have hChildSplit (τ : ℝ) (_ : τ ∈ Icc 0 (P.slab 1 0)) :
      child.velocity τ = V τ + tail τ := by
    rw [hChild]
    dsimp only [tail]
    abel
  have hTailBound (τ : ℝ) (hτ : τ ∈ Icc 0 (P.slab 1 0)) :
      SpatialHolderHalf 2 (tail τ) ∧ spatialHolderHalfNorm 2 (tail τ) ≤ P.frequency 2 ^ (-5 : ℝ) :=
    ⟨(hCut.all_tails 2 hDepth τ hτ).1, (hCut.tail_two τ hτ).trans (hTail τ hτ)⟩
  have hT4 := w.child_T4_center hFreq (hMono (by decide)) hr hCell hh hh₁ hSmall
    P.strengthConstant_ge hL (hLife.step 0).1.le hCstep hV hChildSplit hOsc hMean hRem hTailBound
  have hCenter := hT4.1
  have hDelay := hT4.2.1
  have hDelayUpper := hT4.2.2.1
  have hRatio := hT4.2.2.2.1
  have hνlo := hT4.2.2.2.2.1
  have hνhi := hT4.2.2.2.2.2.1
  have hStrengthLo := hT4.2.2.2.2.2.2.1
  have hStrengthHi := hT4.2.2.2.2.2.2.2
  refine {
    stationary := parent
    first := child
    wave := {
      oscillation := osc
      waveVector := w.covector
      amplitude := w.amplitude
      cutoff := fun _ => 1
      error := E
      center := ?_
      activation_step := ⟨hDelay, hDelayUpper⟩
      oscillation_bound := hOscillation
      correction_bound := by simpa only [hChild] using hCorrection
      oscillation_vanishes := fun hnone => by omega
      oscillation_support := hSupport
      gradient_split := ?_
      error_bound := fun τ hτ => (hCenter τ hτ).2
      cutoff_complete := fun _ _ => rfl
      strength_at_crossing := ⟨hStrengthLo, hStrengthHi⟩
      coupling_at_crossing := ?_
      ratio_at_crossing := ?_ }
    initial_coupling := ?_ }
  · rw [hParent]
    exact LocalizedAmplitude.firstWave_parentCenterWaveOn w hFpos hTiltSmall hSmall hD
  · intro τ hτ
    simpa only [hParent, stationaryShearGradient_origin, one_smul, InnerProductSpace.rankOne_def]
      using (hCenter τ hτ).1
  · rw [hParent, stationaryShearGradient_origin]
    exact ⟨hνlo, hνhi⟩
  · rw [hParent, stationaryShearGradient_origin, ← hTilt]
    exact hRatio
  · change entry (frame w.covector w.amplitude 0) (fderiv ℝ (parent.velocity 0) 0) 0 1 = 2 * Real.pi
    rw [hParent, stationaryShearGradient_origin]
    exact (w.initial_couplings hFpos).1

end InductiveEulerBase

/-- Attach the central proof and selected crossing to the same child produced
by the quantitative hierarchy cutoff. The exit coupling is taken from the
certified prefix. -/
def InductiveEulerStep.ofPhysicalHierarchyCutoff
    {P : InductiveEulerParameters} {n depth : ℕ} {hLife : P.LifetimeBounds} {tip : InductiveEulerTip P n}
    (pre : InductiveEulerPrefix P hLife n tip)
    (w : MovingWaveVector.LaterPhysicalWindow tip.older.velocity tip.parent.velocity tip.wave.waveVector
      tip.wave.amplitude tip.wave.error tip.nextActivation (P.slab (n + 2) tip.nextActivation))
    (d : MovingWaveVector.LaterWaveSelection tip.parent.velocity w.physical P.comparisonConstant
      (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
      (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9))
    {Λ C K : ℝ} {ψ : Vec3 → ℝ} {V RV osc : Velocity} {rawError : ℝ → Vec3 →L[ℝ] Vec3}
    (s : TruncatedChildStage (P.slab (n + 2) tip.nextActivation) Λ ψ V RV)
    (child : InductiveEulerStage P (n + 2) tip.nextActivation) (hChild : child.velocity = s.velocity)
    (hLarge : Real.exp 4 ≤ P.frequency 0) (hConst : 18 * Real.exp 3 ≤ P.strengthConstant)
    (hOsc : ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation), ∀ x, ‖osc t x‖ ≤ (P.frequency (n + 2))⁻¹)
    (hCorrection : ∀ m ≤ P.order (n + 2), ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation),
      let v := child.velocity t - tip.parent.velocity t - osc t
      SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (P.frequency (n + 2))⁻¹)
    (hVanish : ∀ t ∈ Icc 0 tip.nextActivation, osc t = 0)
    (hSupport : ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation), ∀ x, osc t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency (n + 1))⁻¹)
    (approximatePressure : ℝ → EndpointSmoothPotential)
    (hCutoff : s.CutoffBounds approximatePressure depth C K) (hDepth : 2 ≤ depth)
    (hTail : ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation),
      K * s.truncationError depth t ≤ P.frequency (n + 3) ^ (-5 : ℝ))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 (P.slab (n + 2) tip.nextActivation) ×ˢ
      (univ : Set Vec3)))
    (hApprox : ∀ t ∈ Icc tip.nextActivation (P.slab (n + 2) tip.nextActivation),
      fderiv ℝ (V t) 0 = fderiv ℝ (tip.parent.velocity t) 0 +
        waveSwitch tip.nextActivation w.physical.rate t •
          InnerProductSpace.rankOne ℝ (d.crossing.amplitude t) (d.crossing.waveVector t) + rawError t ∧
      ‖rawError t‖ ≤ P.frequency (n + 2) ^ (-1 / 3 : ℝ)) :
    InductiveEulerStep tip := by
  have hInitial : 2 ≤ P.frequency 0 := by
    have h : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    exact h.trans hLarge
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (one_le_two.trans hInitial) P.frequency_step
  have hμ : 2 ≤ P.frequency (n + 1) := hInitial.trans (hMono (Nat.zero_le _))
  have hRatio : w.physical.ratio = couplingRatioOfGain (4 * Real.log (P.frequency (n + 3))) := by
    unfold PhysicalAmplification.ratio PhysicalAmplification.firstCoupling
      PhysicalAmplification.thirdCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
    exact tip.wave.ratio_at_crossing
  have hStrength := InductiveEulerWave.growingCrossingStrength d.crossing rfl hLarge hConst hRatio
  have hAt : d.crossing.crossing ∈ Icc tip.nextActivation (P.slab (n + 2) tip.nextActivation) :=
    ⟨d.crossing.crossing_in_slab.1, d.crossing.crossing_in_slab.2.trans_eq d.clock_eq⟩
  have hCoupling := pre.later_wave_exit_coupling hLarge w d
  have hCoupling' : Real.pi ≤ w.physical.physicalNu d.crossing.waveVector d.crossing.amplitude d.crossing.crossing ∧
      w.physical.physicalNu d.crossing.waveVector d.crossing.amplitude d.crossing.crossing ≤ 4 * Real.pi := by
    simp only [PhysicalAmplification.physicalNu, w.parent_gradient_eq hAt]
    exact ⟨hCoupling.1,hCoupling.2.1⟩
  let wave := InductiveEulerWave.ofGrowingCrossingCutoff tip.parent child s hChild d.crossing
    hμ tip.next_activation_nonnegative d.clock_eq d.crossing_in_first_half w.parent_gradient_eq d.center
    hOsc (by simpa only [hChild] using hCorrection) (fun _ => hVanish) hSupport
    approximatePressure hCutoff hDepth hTail hV hApprox hStrength hCoupling'
  exact InductiveEulerStep.ofLaterWaveSelection tip w d child wave rfl rfl

section Scheduled

variable {P : InductiveEulerParameters} {n : ℕ} {activationOld activation : ℝ}

local notation "Tchild" => P.slab (n + 1) activation
local notation "Tparent" => P.slab n activationOld
local notation "parentFrequency" => P.frequency n
local notation "childFrequency" => P.frequency (n + 1)
local notation "nextFrequency" => P.frequency (n + 2)
local notation "order" => P.order (n + 1)
local notation "nextOrder" => P.order (n + 2)
local notation "depth" => 6 * frequencyExponent P.exponentParameter nextOrder

/-- Eulerian estimates of the finite hierarchy before the Fourier cutoff. -/
structure PhysicalWaveApproximationBounds
    (parent : InductiveEulerStage P n activationOld) (activation : ℝ)
    (V RV oscillation mean : Velocity) (approximatePressure : ℝ → EndpointSmoothPotential)
    (Cstep Cmean : ℝ) : Prop where
  velocity_size : ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
    1 + spatialHolderHalfNorm depth (V t) ≤ 3 * childFrequency ^ (2 * (depth + 1))
  residual_size : ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
    spatialHolderHalfNorm 1 (RV t) ≤ nextFrequency ^ (-7 / 2 : ℝ)
  oscillation_size : ∀ t ∈ Icc 0 (P.slab (n + 1) activation), ∀ x,
    ‖oscillation t x‖ ≤ Cstep * childFrequency ^ (-5 / 4 : ℝ)
  mean_size : ∀ m ≤ order, ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
    SpatialHolderHalf m (mean t) ∧
      spatialHolderHalfNorm m (mean t) ≤
        Cmean * (parentFrequency ^ 9) ^ (P.exponentParameter * (m + 2)) *
          childFrequency ^ (-5 / 2 : ℝ)
  pressure_upper : ∀ t ∈ Icc 0 (P.slab (n + 1) activation), ∀ x v : Vec3,
    ⟪v, fderiv ℝ (gradient (approximatePressure t).lift) x v⟫_ℝ ≤
      ⟪v, fderiv ℝ (gradient (parent.pressure t)) x v⟫_ℝ +
        (Cstep * childFrequency ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2

private theorem physicalWave_schedule (hInitial : 2 ≤ P.frequency 0) :
    2 ≤ parentFrequency ∧ order ≤ nextOrder ∧ max 2 order ≤ depth := by
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (one_le_two.trans hInitial) P.frequency_step
  have hOrder := (frequencySchedule_order_steps P.threshold P.frequency P.order P.initial_order
    P.initial_threshold hMono P.order_maximum n).1
  have hExponent : nextOrder + 1 ≤ frequencyExponent P.exponentParameter nextOrder := by
    unfold frequencyExponent
    exact Nat.le_mul_of_pos_left _ (by have := P.exponentParameter_ge; positivity)
  have hDepth : 2 * (nextOrder + 1) ≤ depth := by omega
  exact ⟨hInitial.trans (hMono (Nat.zero_le n)), hOrder, max_le (by omega) (by omega)⟩

local notation "scheduledFrequency" => parentFrequency ^ frequencyExponent P.exponentParameter order
local notation "scheduledNext" => scheduledFrequency ^ frequencyExponent P.exponentParameter nextOrder

private theorem physicalWave_next_frequency :
    nextFrequency = scheduledNext := by
  rw [P.frequency_step (n + 1), P.frequency_step n]

/-- Apply the scheduled cutoff estimates to the same physical field on which
the deformation estimate is established. -/
theorem exists_inductiveEulerChild_of_physicalCutoff
    (parent : InductiveEulerStage P n activationOld)
    {V RV oscillation mean : Velocity} {ψ : Vec3 → ℝ}
    (s : TruncatedChildStage Tchild (scheduledFrequency ^ 5) ψ V RV)
    (approximatePressure : ℝ → EndpointSmoothPotential)
    {C K Cstep Cmean : ℝ} {Y : ℝ → Velocity}
    (hB : s.CutoffBounds approximatePressure depth C K)
    (hApprox : PhysicalWaveApproximationBounds parent activation V RV oscillation mean
      approximatePressure Cstep Cmean)
    (hInitial : 2 ≤ P.frequency 0) (hSlab : Tchild ≤ Tparent)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKμ : K ≤ parentFrequency) (hMeanμ : Cmean ≤ parentFrequency)
    (hCstep : Cstep ≤ childFrequency ^ (1 / 32 : ℝ))
    (hLarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ nextFrequency)
    (hV : ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf depth (V t))
    (hSplit : ∀ t ∈ Icc 0 Tchild, V t = parent.velocity t + oscillation t + mean t)
    (hFlow : ChildFlow.DeformationOn s.velocity Y Tchild (Cstep * childFrequency ^ (1 / 4 : ℝ))) :
    ∃ child : InductiveEulerStage P (n + 1) activation,
      child.velocity = s.velocity ∧ child.pressure = s.pressure ∧
      (∀ t ∈ Icc 0 Tchild, ∀ x, ‖oscillation t x‖ ≤ childFrequency⁻¹) ∧
      ∀ m ≤ order, ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf m (child.velocity t - parent.velocity t - oscillation t) ∧
        spatialHolderHalfNorm m (child.velocity t - parent.velocity t - oscillation t) ≤ childFrequency⁻¹ := by
  obtain ⟨hμ, hOrder, hDepth⟩ := physicalWave_schedule (P := P) (n := n) hInitial
  have hChildEq : childFrequency = scheduledFrequency := P.frequency_step n
  have hNextEq : nextFrequency = scheduledNext := physicalWave_next_frequency
  have hFreq : 1 ≤ scheduledFrequency := one_le_pow₀ (by linarith)
  have hErr (t : ℝ) (ht : t ∈ Icc 0 Tchild) :
      K * s.truncationError depth t ≤ scheduledNext ^ (-5 : ℝ) :=
    s.truncationError_le_next hμ P.exponentParameter_ge hKμ t (hV t ht)
      (by simpa only [hChildEq] using hApprox.velocity_size t ht)
  have hInc := s.scheduled_increment approximatePressure hB hμ P.exponentParameter_ge hOrder
    ((le_max_right 2 order).trans hDepth) hMeanμ hK hV hSplit
    (by simpa only [hChildEq] using hApprox.mean_size) hErr
  have hParent (t : ℝ) (ht : t ∈ Icc 0 Tchild) (x : Vec3) : ‖parent.velocity t x‖ ≤ parentFrequency :=
    ((parent.torusVelocity t).norm_coe_le_norm _).trans (parent.velocity_bound t ⟨ht.1, ht.2.trans hSlab⟩)
  have hT := s.scheduled_T2_T3 approximatePressure hB hμ P.exponentParameter_ge hC hSlab
    (by simpa only [hChildEq] using hCstep) (by simpa only [hNextEq] using hLarge)
    (by simpa only [hChildEq] using hFlow) hParent
    (by simpa only [hChildEq] using hApprox.oscillation_size) (hInc 0 (Nat.zero_le _))
    (by simpa only [hNextEq] using hApprox.residual_size) hErr parent.pressure_hessian
    (by simpa only [hChildEq] using hApprox.pressure_upper)
  obtain ⟨hU, hY, hR, hPress⟩ := hT
  have hRadius : scheduledFrequency ^ (5 : ℕ) = childFrequency ^ (5 : ℕ) := by rw [hChildEq]
  have hInU (t : ℝ) (ht : t ∈ Icc 0 Tchild) : ‖s.torusVelocity t‖ ≤ childFrequency :=
    (hU t ht).trans_eq hChildEq.symm
  have hInFlow : ChildFlow.DeformationOn s.velocity Y Tchild childFrequency := by rwa [hChildEq]
  have hInR (t : ℝ) (ht : t ∈ Icc 0 Tchild) (x : Vec3) :
      ‖s.residual t x‖ ≤ nextFrequency ^ (-3 : ℝ) := by rw [hNextEq]; exact hR t ht x
  let child := InductiveEulerStage.ofTruncatedChildStage s rfl hRadius hInU hInFlow hInR hPress
  have hVel : child.velocity = s.velocity := InductiveEulerStage.ofTruncatedChildStage_velocity _ _ _ _ _ _ _
  have hPressEq : child.pressure = s.pressure :=
    InductiveEulerStage.ofTruncatedChildStage_pressure _ _ _ _ _ _ _
  have hOsc := (induction_child_oscillation_and_deformation_budget hFreq
    (by simpa only [hChildEq] using hCstep)).1
  refine ⟨child, hVel, hPressEq, fun t ht x => ?_, ?_⟩
  · rw [hChildEq]
    exact (hApprox.oscillation_size t ht x).trans (by simpa only [hChildEq] using hOsc)
  · simpa only [hChildEq,hVel] using hInc

/-- Close the next physical stage using the quantified profile jet bounds and its actual cutoff.
The deformation is obtained from the child-flow theorem on the same cutoff tail. -/
theorem exists_inductiveEulerChild_of_profileJets
    (parent : InductiveEulerStage P n activationOld)
    {V RV oscillation mean : Velocity} {ψ : Vec3 → ℝ}
    (s : TruncatedChildStage Tchild (scheduledFrequency ^ 5) ψ V RV)
    (approximatePressure : ℝ → EndpointSmoothPotential)
    (W : ℝ → Vec3 → ℝ → Vec3) {k : Vec3}
    {C K Cmean D ell h B Γ : ℝ} {a p bFlow : ℕ}
    (hCutoff : s.CutoffBounds approximatePressure depth C K)
    (hApprox : PhysicalWaveApproximationBounds parent activation V RV oscillation mean
      approximatePressure (Γ * D ^ bFlow) Cmean)
    (hInitial : 2 ≤ P.frequency 0) (hSlab : Tchild ≤ Tparent)
    (hT : 0 < Tchild) (hT₁ : Tchild ≤ 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKμ : K ≤ parentFrequency) (hMeanμ : Cmean ≤ parentFrequency)
    (hCstep : Γ * D ^ bFlow ≤ childFrequency ^ (1 / 32 : ℝ))
    (hLarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ nextFrequency)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 Tchild ×ˢ (univ : Set Vec3)))
    (hDiv : ∀ t ∈ Icc 0 Tchild, ∀ x, divergence (V t) x = 0)
    (hSplit : ∀ t ∈ Icc 0 Tchild, V t = parent.velocity t + oscillation t + mean t)
    (hVeq : ∀ t ∈ Icc 0 Tchild, ∀ x,
      V t x = parent.velocity t x + transportedProfile (fun r => parent.flow r 0) k W t x)
    (hDom : parentFrequency ≤ D) (hell : 0 < ell) (hB : 0 ≤ B)
    (hellSize : ell⁻¹ ≤ D ^ a) (hh : h = childFrequency ^ (-1 / 2 : ℝ))
    (hk : ‖k‖ ≤ D * childFrequency)
    (hb : max a 1 + (max a 1 + p) + 1 ≤ bFlow) (hΓ : 1 + 40 * B ≤ Γ)
    (hW : ∀ t ∈ Icc 0 Tchild, ContDiff ℝ ∞ (Function.uncurry (W t)))
    (hWp : ∀ t ∈ Icc 0 Tchild, ∀ x, Function.Periodic (W t x) 1)
    (hWskew : ∀ t ∈ Icc 0 Tchild, ∀ (m : Fin 3 → ℤ) x r,
      W t (x + latticeVector m) (r + ⟪k, latticeVector m⟫_ℝ) = W t x r)
    (hWdiv : ∀ t ∈ Icc 0 Tchild, ∀ x r,
      divergence (fun y => W t (parent.flow t 0 y) r) (parent.flow 0 t x) +
      ⟪(fderiv ℝ (parent.flow t 0) (parent.flow 0 t x)).adjoint k, deriv (W t x) r⟫_ℝ = 0)
    (hJets : s.PulledBackProfileJetBounds parent.flow W childFrequency ell h B D p) :
    ∃ child : InductiveEulerStage P (n + 1) activation,
      child.velocity = s.velocity ∧ child.pressure = s.pressure ∧
      (∀ t ∈ Icc 0 Tchild, ∀ x, ‖oscillation t x‖ ≤ childFrequency⁻¹) ∧
      ∀ m ≤ order, ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf m (child.velocity t - parent.velocity t - oscillation t) ∧
        spatialHolderHalfNorm m (child.velocity t - parent.velocity t - oscillation t) ≤ childFrequency⁻¹ := by
  obtain ⟨hμ, _, hDepth⟩ := physicalWave_schedule (P := P) (n := n) hInitial
  have hChildEq : childFrequency = scheduledFrequency := P.frequency_step n
  have hNextEq : nextFrequency = scheduledNext := physicalWave_next_frequency
  have hFreq : 1 ≤ childFrequency := by rw [hChildEq]; exact one_le_pow₀ (by linarith)
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (one_le_two.trans hInitial) P.frequency_step
  have hNext : childFrequency ≤ nextFrequency := hMono (by omega)
  have hVholder (t : ℝ) (ht : t ∈ Icc 0 Tchild) : SpatialHolderHalf depth (V t) := by
    have hP : SpatiallyPeriodic (V t) := by
      intro m x
      rw [← s.approximate_rep t ht, ← s.approximate_rep t ht,
        (toUnitTorus_eq_iff _ _).mpr ⟨m,rfl⟩]
    exact spatialHolderHalf_of_contDiff_periodic (physicalWave_slice_smooth hV ht) hP depth
  have hErr (t : ℝ) (ht : t ∈ Icc 0 Tchild) : K * s.truncationError depth t ≤ nextFrequency ^ (-5 : ℝ) := by
    rw [hNextEq]
    exact s.truncationError_le_next hμ P.exponentParameter_ge hKμ t (hVholder t ht)
      (by simpa only [hChildEq] using hApprox.velocity_size t ht)
  have hSub : Icc 0 Tchild ⊆ Icc 0 Tparent := Icc_subset_Icc_right hSlab
  have hX : IsLabelFlowOn parent.velocity parent.flow (Icc 0 Tchild) := by
    refine ⟨fun t ht => parent.deformation.flow.initial t (hSub ht), ?_⟩
    intro t ht x r hr
    exact (parent.deformation.flow.trajectory t (hSub ht) x r (hSub hr)).mono hSub
  have hU : ContDiffOn ℝ ∞ (Function.uncurry parent.velocity) (Icc 0 Tchild ×ˢ (univ : Set Vec3)) :=
    parent.smooth_velocity.mono (prod_mono_left hSub)
  have hUper (t : ℝ) (_ : t ∈ Icc 0 Tchild) : SpatiallyPeriodic (parent.velocity t) :=
    parent.periodic_velocity t
  have hXsmooth := hX.contDiffOn_forwardLabelFlow hT hU hUper
  have hX2 (t : ℝ) (ht : t ∈ Icc 0 Tchild) (x : Vec3) : ContDiffAt ℝ 2 (parent.flow 0 t) x :=
    ((physicalWave_slice_smooth hXsmooth ht).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
  have hD (t : ℝ) (ht : t ∈ Icc 0 Tchild) (x : Vec3) :
      ‖fderiv ℝ (parent.flow 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (parent.flow t 0) x‖ ≤ D :=
    ⟨((parent.deformation.bounds t (hSub ht)).2.1 x).2.trans hDom,
      ((parent.deformation.bounds t (hSub ht)).2.2 x).2.trans hDom⟩
  have hSmall : Γ * D ^ bFlow * childFrequency ^ (-1 / 12 : ℝ) ≤ 1 := calc
    _ ≤ childFrequency ^ (1 / 32 : ℝ) * childFrequency ^ (-1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_right hCstep (by positivity)
    _ = childFrequency ^ (-5 / 96 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hFreq)]
      norm_num
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hFreq (by norm_num)
  obtain ⟨Y,hY⟩ := s.exists_childFlow_of_profile_jet_bounds approximatePressure
    hCutoff hV hDiv ((le_max_left 2 order).trans hDepth) hNext hErr hVeq hT hT₁
    hX (hU.of_le (by simp)) hUper (fun t ht => parent.divergence_free t (hSub ht)) hX2 hD
    ((one_le_two.trans hμ).trans hDom) hFreq hell hB hellSize hh hk hb hΓ hSmall
    hW hWp hWskew hWdiv hJets
  exact exists_inductiveEulerChild_of_physicalCutoff parent s approximatePressure hCutoff hApprox
    hInitial hSlab hC hK hKμ hMeanμ hCstep hLarge hVholder hSplit hY

open HierarchyTwistedProfile

/-- Close the child of the actual finite hierarchy on the physical graph.
The only remaining analytic inputs are the scalar budgets and the measured
Eulerian and pulled-back profile bounds. -/
theorem exists_inductiveEulerChild_of_actualHierarchy
    (parent : InductiveEulerStage P n activationOld) {k : Vec3}
    {hT : 0 < Tchild} {d : ParentGeometry hT parent.velocity parent.flow k}
    (b : PhysicalApproximationData d parent.pressure depth) (properties : PhysicalApproximationProperties b)
    {ψ : Vec3 → ℝ} (s : TruncatedChildStage Tchild (scheduledFrequency ^ 5) ψ b.velocity b.residual)
    {C K Cmean D ell h B Γ : ℝ} {a p bFlow : ℕ}
    (hCutoff : s.CutoffBounds (b.potential properties) depth C K)
    (hApprox : PhysicalWaveApproximationBounds parent activation
      b.velocity b.residual b.oscillation b.meanCorrection (b.potential properties) (Γ * D ^ bFlow) Cmean)
    (hInitial : 2 ≤ P.frequency 0) (hSlab : Tchild ≤ Tparent)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKμ : K ≤ parentFrequency) (hMeanμ : Cmean ≤ parentFrequency)
    (hCstep : Γ * D ^ bFlow ≤ childFrequency ^ (1 / 32 : ℝ))
    (hLarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ nextFrequency)
    (hDom : parentFrequency ≤ D) (hell : 0 < ell) (hB : 0 ≤ B)
    (hellSize : ell⁻¹ ≤ D ^ a) (hh : h = childFrequency ^ (-1 / 2 : ℝ))
    (hk : ‖k‖ ≤ D * childFrequency)
    (hb : max a 1 + (max a 1 + p) + 1 ≤ bFlow) (hΓ : 1 + 40 * B ≤ Γ)
    (hJets : s.PulledBackProfileJetBounds parent.flow b.profileVelocity childFrequency ell h B D p) :
    ∃ child : InductiveEulerStage P (n + 1) activation,
      child.velocity = s.velocity ∧ child.pressure = s.pressure ∧
      (∀ t ∈ Icc 0 Tchild, ∀ x, ‖b.oscillation t x‖ ≤ childFrequency⁻¹) ∧
      ∀ m ≤ order, ∀ t ∈ Icc 0 Tchild,
        SpatialHolderHalf m (child.velocity t - parent.velocity t - b.oscillation t) ∧
        spatialHolderHalfNorm m (child.velocity t - parent.velocity t - b.oscillation t) ≤ childFrequency⁻¹ := by
  have hSplit (t : ℝ) (_ : t ∈ Icc 0 Tchild) :
      b.velocity t = parent.velocity t + b.oscillation t + b.meanCorrection t :=
    congrFun b.velocity_eq_parent_add_oscillation_add_mean t
  have hGraph (t : ℝ) (_ : t ∈ Icc 0 Tchild) (x : Vec3) :
      b.velocity t x = parent.velocity t x +
        transportedProfile (fun r => parent.flow r 0) k b.profileVelocity t x := rfl
  exact exists_inductiveEulerChild_of_profileJets parent s (b.potential properties) b.profileVelocity
    hCutoff hApprox hInitial hSlab hT b.time_le_one hC hK hKμ hMeanμ hCstep hLarge
    properties.velocity_smooth properties.divergence_free hSplit hGraph hDom hell hB
    hellSize hh hk hb hΓ b.profileVelocity_smooth (fun t _ => b.profileVelocity_periodic t)
    (fun t _ => b.profileVelocity_skew t) properties.profile_divergence hJets

end Scheduled

/-- Close a later step of the dependent induction from the actual graph of
the solved hierarchy and the preceding selected comparison. -/
theorem exists_inductiveEulerStep_of_actualHierarchy
    {P : InductiveEulerParameters} {n : ℕ} {hLife : P.LifetimeBounds} {tip : InductiveEulerTip P n}
    (pre : InductiveEulerPrefix P hLife n tip)
    (w : MovingWaveVector.LaterPhysicalWindow tip.older.velocity tip.parent.velocity tip.wave.waveVector
      tip.wave.amplitude tip.wave.error tip.nextActivation (P.slab (n + 2) tip.nextActivation))
    (d : MovingWaveVector.LaterWaveSelection tip.parent.velocity w.physical P.comparisonConstant
      (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
      (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9))
    {k : Vec3} {hT : 0 < P.slab (n + 2) tip.nextActivation}
    {geom : ParentGeometry hT tip.parent.velocity tip.parent.flow k}
    (b : PhysicalApproximationData geom tip.parent.pressure
      (6 * frequencyExponent P.exponentParameter (P.order (n + 3))))
    (properties : PhysicalApproximationProperties b)
    {ψ : Vec3 → ℝ}
    (s : TruncatedChildStage (P.slab (n + 2) tip.nextActivation)
      ((P.frequency (n + 1) ^ frequencyExponent P.exponentParameter (P.order (n + 2))) ^ 5) ψ
      b.velocity b.residual)
    {C K Cmean D ell h B Γ : ℝ} {a p bFlow : ℕ}
    (hCutoff : s.CutoffBounds (b.potential properties)
      (6 * frequencyExponent P.exponentParameter (P.order (n + 3))) C K)
    (hBounds : PhysicalWaveApproximationBounds tip.parent tip.nextActivation
      b.velocity b.residual b.oscillation b.meanCorrection (b.potential properties) (Γ * D ^ bFlow) Cmean)
    (hLarge : Real.exp 4 ≤ P.frequency 0) (hStrength : 18 * Real.exp 3 ≤ P.strengthConstant)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKμ : K ≤ P.frequency (n + 1)) (hMeanμ : Cmean ≤ P.frequency (n + 1))
    (hCstep : Γ * D ^ bFlow ≤ P.frequency (n + 2) ^ (1 / 32 : ℝ))
    (hNext : max 2 ((2 * C) ^ (2 : ℕ)) ≤ P.frequency (n + 3))
    (hDom : P.frequency (n + 1) ≤ D) (hell : 0 < ell) (hB : 0 ≤ B)
    (hellSize : ell⁻¹ ≤ D ^ a) (hh : h = P.frequency (n + 2) ^ (-1 / 2 : ℝ))
    (hk : ‖k‖ ≤ D * P.frequency (n + 2))
    (hb : max a 1 + (max a 1 + p) + 1 ≤ bFlow) (hΓ : 1 + 40 * B ≤ Γ)
    (hJets : s.PulledBackProfileJetBounds tip.parent.flow b.profileVelocity
      (P.frequency (n + 2)) ell h B D p)
    (hVanish : ∀ r ∈ Icc 0 tip.nextActivation, b.oscillation r = 0)
    (hSupport : ∀ r ∈ Icc 0 (P.slab (n + 2) tip.nextActivation), ∀ x, b.oscillation r x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency (n + 1))⁻¹)
    (rawError : ℝ → Vec3 →L[ℝ] Vec3)
    (hCenter : ∀ r ∈ Icc tip.nextActivation (P.slab (n + 2) tip.nextActivation),
      fderiv ℝ (b.velocity r) 0 = fderiv ℝ (tip.parent.velocity r) 0 +
        waveSwitch tip.nextActivation w.physical.rate r •
          InnerProductSpace.rankOne ℝ (d.crossing.amplitude r) (d.crossing.waveVector r) + rawError r ∧
      ‖rawError r‖ ≤ P.frequency (n + 2) ^ (-1 / 3 : ℝ)) :
    ∃ step : InductiveEulerStep tip, step.child.velocity = s.velocity ∧ step.child.pressure = s.pressure ∧
      step.wave.oscillation = b.oscillation := by
  have hInitial : 2 ≤ P.frequency 0 := by
    have h : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    exact h.trans hLarge
  obtain ⟨child, hChild, hPressure, hOsc, hCorrection⟩ :=
    exists_inductiveEulerChild_of_actualHierarchy tip.parent b properties s hCutoff hBounds
      hInitial (tip.next_slab_lt hLife).le hC hK hKμ hMeanμ hCstep hNext hDom hell hB
      hellSize hh hk hb hΓ hJets
  obtain ⟨hμ, _, hDepth⟩ := physicalWave_schedule (P := P) (n := n + 1) hInitial
  have hTail (r : ℝ) (hr : r ∈ Icc 0 (P.slab (n + 2) tip.nextActivation)) :
      K * s.truncationError (6 * frequencyExponent P.exponentParameter (P.order (n + 3))) r ≤
        P.frequency (n + 3) ^ (-5 : ℝ) := by
    rw [physicalWave_next_frequency (P := P) (n := n + 1)]
    apply s.truncationError_le_next hμ P.exponentParameter_ge hKμ r
    · exact spatialHolderHalf_of_contDiff_periodic
        (physicalWave_slice_smooth properties.velocity_smooth hr) (properties.periodic r hr).1 _
    · simpa only [P.frequency_step (n + 1)] using hBounds.velocity_size r hr
  refine ⟨InductiveEulerStep.ofPhysicalHierarchyCutoff pre w d s child hChild hLarge hStrength
    hOsc hCorrection hVanish hSupport (b.potential properties) hCutoff
    ((le_max_left _ _).trans hDepth) hTail properties.velocity_smooth hCenter, hChild, hPressure, rfl⟩

/-- Close the base of the induction with the actual localized first wave and
the same pressure and cutoff used to establish its physical stage estimates. -/
theorem exists_inductiveEulerBase_of_actualHierarchy
    {P : InductiveEulerParameters} (parent : InductiveEulerStage P 0 0)
    {tilt radius : ℝ} {k : Vec3} {hT : 0 < P.slab 1 0}
    {geom : ParentGeometry hT parent.velocity parent.flow k}
    (b : PhysicalApproximationData geom parent.pressure
      (6 * frequencyExponent P.exponentParameter (P.order 2)))
    (properties : PhysicalApproximationProperties b)
    {ψ : Vec3 → ℝ}
    (s : TruncatedChildStage (P.slab 1 0)
      ((P.frequency 0 ^ frequencyExponent P.exponentParameter (P.order 1)) ^ 5) ψ b.velocity b.residual)
    (w : FirstWaveOrigin tilt (P.slab 1 0) (P.frequency 1))
    (hLife : P.LifetimeBounds) (hInitial : 2 ≤ P.frequency 0)
    {C K Cmean D ell h B Γ : ℝ} {a p bFlow : ℕ}
    (hCutoff : s.CutoffBounds (b.potential properties)
      (6 * frequencyExponent P.exponentParameter (P.order 2)) C K)
    (hBounds : PhysicalWaveApproximationBounds parent 0 b.velocity b.residual b.oscillation b.meanCorrection
      (b.potential properties) (Γ * D ^ bFlow) Cmean)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKμ : K ≤ P.frequency 0) (hMeanμ : Cmean ≤ P.frequency 0)
    (hCstep : Γ * D ^ bFlow ≤ P.frequency 1 ^ (1 / 32 : ℝ))
    (hNext : max 2 ((2 * C) ^ (2 : ℕ)) ≤ P.frequency 2)
    (hDom : P.frequency 0 ≤ D) (hell : 0 < ell) (hB : 0 ≤ B)
    (hellSize : ell⁻¹ ≤ D ^ a) (hh : h = P.frequency 1 ^ (-1 / 2 : ℝ))
    (hk : ‖k‖ ≤ D * P.frequency 1)
    (hb : max a 1 + (max a 1 + p) + 1 ≤ bFlow) (hΓ : 1 + 40 * B ≤ Γ)
    (hJets : s.PulledBackProfileJetBounds parent.flow b.profileVelocity (P.frequency 1) ell h B D p)
    (hTilt : tilt = couplingRatioOfGain (4 * Real.log (P.frequency 3)))
    (hTiltSmall : |tilt| ≤ 1) (hL : 1 ≤ 4 * Real.log (P.frequency 3))
    (hParent : parent.velocity = fun _ => stationaryShear tilt)
    (hr : 0 < radius) (hCell : 2 * radius < 1 / 2)
    (hSmall : P.slab 1 0 * ‖stationaryShearGradient tilt‖ ≤ 1 / 8)
    (hSupport : ∀ τ ∈ Icc 0 (P.slab 1 0), ∀ x, b.oscillation τ x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency 0)⁻¹)
    (oscillatoryRemainder : Velocity)
    (hSplit : ∀ τ ∈ Icc 0 (P.slab 1 0), b.velocity τ = stationaryShear tilt +
      localizedTransportedProfile (fun u => stationaryShearFlow tilt (-u))
        (P.frequency 1 • EuclideanSpace.single 0 1) (firstWaveLeadingProfile tilt w.scale radius h) τ +
      oscillatoryRemainder τ + b.meanCorrection τ)
    (hOsc : ∀ τ ∈ Icc 0 (P.slab 1 0), DifferentiableAt ℝ (oscillatoryRemainder τ) 0)
    (hRem : ∀ τ ∈ Icc 0 (P.slab 1 0), ‖fderiv ℝ (oscillatoryRemainder τ) 0‖ +
      ‖fderiv ℝ (b.meanCorrection τ) 0‖ ≤ (Γ * D ^ bFlow) * P.frequency 1 ^ (-5 / 12 : ℝ)) :
    ∃ base : InductiveEulerBase P, base.first.velocity = s.velocity ∧ base.first.pressure = s.pressure ∧
      base.stationary = parent ∧ base.wave.oscillation = b.oscillation := by
  have hSlab : P.slab 1 0 ≤ P.slab 0 0 := by
    rw [P.slab_succ, P.slab_zero]
    linarith [hLife.first]
  obtain ⟨child, hChild, hPressure, hOscillation, hCorrection⟩ :=
    exists_inductiveEulerChild_of_actualHierarchy parent b properties s hCutoff hBounds
      hInitial hSlab hC hK hKμ hMeanμ hCstep hNext hDom hell hB hellSize hh hk hb hΓ hJets
  obtain ⟨hμ, _, hDepth⟩ := physicalWave_schedule (P := P) (n := 0) hInitial
  have hTail (r : ℝ) (hr : r ∈ Icc 0 (P.slab 1 0)) :
      K * s.truncationError (6 * frequencyExponent P.exponentParameter (P.order 2)) r ≤
        P.frequency 2 ^ (-5 : ℝ) := by
    rw [physicalWave_next_frequency (P := P) (n := 0)]
    apply s.truncationError_le_next hμ P.exponentParameter_ge hKμ r
    · exact spatialHolderHalf_of_contDiff_periodic
        (physicalWave_slice_smooth properties.velocity_smooth hr) (properties.periodic r hr).1 _
    · simpa only [P.frequency_step 0] using hBounds.velocity_size r hr
  have hFreq : 1 ≤ P.frequency 1 := by
    rw [P.frequency_step 0]
    exact one_le_pow₀ (one_le_two.trans hInitial)
  have hh₀ : 0 < h := by rw [hh]; exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hFreq) _
  have hh₁ : h ≤ 1 := by rw [hh]; exact Real.rpow_le_one_of_one_le_of_nonpos hFreq (by norm_num)
  let base := InductiveEulerBase.ofFirstWaveCutoff parent child s hChild w hLife hμ hTilt hTiltSmall
    hL hParent hr hCell hh₀ hh₁ hSmall hCstep hOscillation
    (by simpa only [hChild] using hCorrection) hSupport (b.potential properties) hCutoff
    ((le_max_left _ _).trans hDepth) hTail hSplit hOsc
    (fun τ ht => (physicalWave_slice_smooth properties.mean_smooth ht).differentiable (by simp) 0)
    hRem
  exact ⟨base, hChild, hPressure, rfl, rfl⟩

end

end TorusEuler
