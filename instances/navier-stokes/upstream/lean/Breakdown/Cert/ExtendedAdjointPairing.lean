import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.TestPairing

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedAdjointPairing

theorem adjoint_isPeriodicField {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {j : Fin k} (hj : j ∈ d.adjointSet) {q : Fin k → ℝ}
    (hq : q ∈ d.params) : IsPeriodicField (d.adjoint j q) := by
  refine ⟨hd.adjoint_measurable j hj q hq, hd.adjoint_periodic j hj q hq, ?_⟩
  unfold periodLIntegral
  calc (∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖d.adjoint j q σ y‖ ^ 2))
      ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (d.adjointL2 j ^ 2) :=
        lintegral_mono fun σ => hd.adjoint_l2 j hj q hq σ
    _ < ⊤ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem lintegral_sq_eq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (g : Lp E 2 μ) :
    ∫⁻ a, ENNReal.ofReal (‖(g : α → E) a‖ ^ 2) ∂μ = ENNReal.ofReal (‖g‖ ^ 2) := by
  have hint : Integrable (fun a => ‖(g : α → E) a‖ ^ 2) μ :=
    (L2.integrable_inner (𝕜 := ℝ) g g).congr (ae_of_all _ fun a => real_inner_self_eq_norm_sq _)
  have h2 : ‖g‖ ^ 2 = ∫ a, ‖(g : α → E) a‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (ae_of_all _ fun a => real_inner_self_eq_norm_sq _)
  rw [h2, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun a => sq_nonneg _)]

theorem coe_ae_of_toLpOrZero {F : Space → Space} {c : L2R} (hm : MemLp F 2)
    (h : toLpOrZero 2 F = c) : (c : Space → Space) =ᵐ[volume] F := by
  rw [← h, toLpOrZero, dif_pos hm]
  exact hm.coeFn_toLp

theorem pairing_eq_inner {F Z : ℝ → Space → Space} {f z : Lp (α := TimeCircle) L2R 2}
    (hf : ∀ᵐ σ : ℝ, ((f (σ : TimeCircle) : Space → Space) =ᵐ[volume] F σ))
    (hz : ∀ᵐ σ : ℝ, ((z (σ : TimeCircle) : Space → Space) =ᵐ[volume] Z σ)) :
    periodPairing F Z = inner ℝ f z := by
  unfold periodPairing
  rw [L2.inner_def f z]
  refine Eq.trans ?_ (integral_Icc_coe (fun t : TimeCircle => inner ℝ (f t) (z t)))
  refine setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [hf, hz] with σ h1 h2 _
  rw [L2.inner_def (f (σ : TimeCircle)) (z (σ : TimeCircle))]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with y e1 e2
  rw [e1, e2]

theorem inner_sub_proj_proj (hP : ProjectionHolds) (x : L2R) :
    inner ℝ (x - toPhysH (solProj x)) (toPhysH (solProj x)) = 0 := by
  rw [inner_sub_left, ← hP.2.2.1, ← hP.2.2.1, hP.2.2.2, sub_self]

theorem inner_sub_proj_self (hP : ProjectionHolds) (x : L2R) :
    inner ℝ (x - toPhysH (solProj x)) x = ‖x - toPhysH (solProj x)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_sub_right (x - toPhysH (solProj x)) x,
    inner_sub_proj_proj hP, sub_zero]

theorem isWeakGradient_of_zero {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hf : ∀ y, f y = 0) (hg : ∀ y, g y = 0) : IsWeakGradient f g := by
  have hf' : f = 0 := funext hf
  have hg' : g = 0 := funext hg
  subst hf' hg'
  exact ⟨locallyIntegrable_zero, locallyIntegrable_zero, fun φ _ i => by simp⟩

theorem zero_isPerturbation (Γ : Set Symmetry) (P : ℝ) : IsPerturbation Γ P 0 0 0 0 where
  measurable_velocity :=
    show AEStronglyMeasurable (fun _ : ℝ × Space => (0 : Space)) volume from aestronglyMeasurable_const
  measurable_gradient :=
    show AEStronglyMeasurable (fun _ : ℝ × Space => (0 : Space →L[ℝ] Space)) volume from
      aestronglyMeasurable_const
  measurable_secondDeriv :=
    show AEStronglyMeasurable (fun _ : ℝ × Space => (0 : Space →L[ℝ] Space →L[ℝ] Space)) volume from
      aestronglyMeasurable_const
  measurable_derivative :=
    show AEStronglyMeasurable (fun _ : ℝ × Space => (0 : Space)) volume from aestronglyMeasurable_const
  periodic_velocity := fun _ _ => rfl
  periodic_gradient := fun _ _ => rfl
  periodic_secondDeriv := fun _ _ => rfl
  periodic_derivative := fun _ _ => rfl
  weak_gradient := ae_of_all _ fun _ => isWeakGradient_of_zero (fun _ => rfl) (fun _ => rfl)
  weak_secondDeriv := ae_of_all _ fun _ _ => isWeakGradient_of_zero (fun _ => by simp)
    (fun _ => by ext; simp)
  divergence_free := ae_of_all _ fun _ => ae_of_all _ fun _ => by simp
  sixth_power := ae_of_all _ fun _ => by simp
  gradient_finite := by simp [periodLIntegral, matSq]
  sumSecondPartials_finite := by simp [periodLIntegral, secondDerivTrace]
  derivative_finite := by simp [periodLIntegral]
  transport := fun _ _ => by simp
  invariant := fun _ _ => ae_of_all _ fun _ => by simp

end Internal.ExtendedAdjointPairing

set_option maxHeartbeats 1000000 in
open Internal.ExtendedAdjointPairing in
theorem extendedAdjointPairingHolds_of (hP : ProjectionHolds) (hT : TestPairingHolds) :
    ExtendedAdjointPairingHolds := by
  intro k d hd j hj q hq
  have hZ : IsPeriodicField (d.adjoint j q) := adjoint_isPeriodicField hd hj hq
  refine ⟨hZ, ?_⟩
  obtain ⟨c, hcZ, hcae⟩ := Internal.TestPairing.exists_curve (d.adjoint j q) hZ
  have hcZ' : ∀ᵐ σ : ℝ, ((c (σ : TimeCircle) : Space → Space) =ᵐ[volume] d.adjoint j q σ) :=
    hcae.mono fun σ h => coe_ae_of_toLpOrZero h.1 h.2
  obtain ⟨e, he⟩ : ∃ e : Lp (α := TimeCircle) L2R 2,
      ∀ᵐ t : TimeCircle, e t = toPhysH (solProj (c t)) := by
    have h := ContinuousLinearMap.coeFn_compLpL (toPhysH.comp solProj) c
    refine ⟨ContinuousLinearMap.compLpL 2 volume (toPhysH.comp solProj) c, h.mono fun t ht => ?_⟩
    rw [ht]
    rfl
  have hsub : ∀ᵐ t : TimeCircle, (c - e) t = c t - toPhysH (solProj (c t)) := by
    filter_upwards [Lp.coeFn_sub c e, he] with t h1 h2
    rw [h1, Pi.sub_apply, h2]
  obtain ⟨D, hDm, hDp, hDae⟩ := exists_joint_representative (p := 2) (c - e)
  have hmeas : AEMeasurable (fun t : TimeCircle => ENNReal.ofReal (‖(c - e) t‖ ^ 2)) volume :=
    ((Lp.aestronglyMeasurable (c - e)).norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hDfin : periodLIntegral (fun σ y => ‖D σ y‖ ^ 2) < ⊤ := by
    have h1 : periodLIntegral (fun σ y => ‖D σ y‖ ^ 2) =
        ∫⁻ σ in Icc (0 : ℝ) 1, ENNReal.ofReal (‖(c - e) (σ : TimeCircle)‖ ^ 2) := by
      unfold periodLIntegral
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hDae] with σ hσ
      rw [← lintegral_sq_eq]
      exact lintegral_congr_ae (hσ.mono fun y hy => by simp only [hy])
    have h2 := lintegral_Icc_coe (fun t : TimeCircle => ENNReal.ofReal (‖(c - e) t‖ ^ 2)) hmeas
    rw [h1, h2, lintegral_sq_eq]
    exact ENNReal.ofReal_lt_top
  have hD : IsPeriodicField D := ⟨hDm, hDp, hDfin⟩
  have hPD : physToHH D = 0 := by
    obtain ⟨cD, hcD, hcDae⟩ := Internal.TestPairing.exists_curve D hD
    have h0 : ∀ᵐ t : TimeCircle, solProj (cD t) = 0 := by
      rw [ae_coe_iff]
      filter_upwards [hcDae, hDae, JointRepresentativeInternal.ae_coe_of_ae hsub] with σ h1 h2 h3
      have h4 : cD (σ : TimeCircle) = (c - e) (σ : TimeCircle) := by
        rw [← h1.2, toLpOrZero, dif_pos h1.1]
        exact Lp.ext (h1.1.coeFn_toLp.trans h2.symm)
      rw [h4, h3, map_sub, hP.2.2.2, sub_self]
    refine Lp.ext (hcD.trans ?_)
    filter_upwards [h0, Lp.coeFn_zero (E := HBar) (p := 2) (μ := (volume : Measure TimeCircle))]
      with t h1 h2
    exact h1.trans h2.symm
  have hRS : IsRightSide (d.profile q) d.actuator 0 0 0 0 D := by
    intro φ hφ
    rw [← hT D hD φ hφ, hPD, inner_zero_left]
    simp [matInner]
  have hdef := hd.adjoint_defect j hj q hq 0 0 0 0 (zero_isPerturbation _ _) D hDm hDp hDfin hRS
  have hw : weightedEnergy d.weightFn 0 0 = 0 := by
    simp [weightedEnergy, periodLIntegral, secondDerivTrace, matSq]
  have hpin : ∀ l, pinValue (d.pin l) 0 = 0 := fun l => by simp [pinValue, matInner]
  simp only [hw, hpin, Real.sqrt_zero, mul_zero, Finset.sum_const_zero, sub_zero,
    abs_nonpos_iff] at hdef
  have hpair : periodPairing D (d.adjoint j q) = inner ℝ (c - e) c := pairing_eq_inner hDae hcZ'
  have hnorm : inner ℝ (c - e) c = ‖c - e‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def (c - e) c, L2.inner_def (c - e) (c - e)]
    refine integral_congr_ae ?_
    filter_upwards [hsub] with t ht
    rw [ht, inner_sub_proj_self hP, real_inner_self_eq_norm_sq]
  have hce : c = e := by
    have h1 : ‖c - e‖ ^ 2 = 0 := by rw [← hnorm, ← hpair]; exact hdef
    exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1))
  intro F hF
  obtain ⟨cF, hcF, hcFae⟩ := Internal.TestPairing.exists_curve F hF
  have hcF' : ∀ᵐ σ : ℝ, ((cF (σ : TimeCircle) : Space → Space) =ᵐ[volume] F σ) :=
    hcFae.mono fun σ h => coe_ae_of_toLpOrZero h.1 h.2
  rw [Internal.TestPairing.inner_eq_of_ae hcF hcZ, pairing_eq_inner hcF' hcZ', L2.inner_def cF c]
  refine (integral_Icc_coe (fun t : TimeCircle => inner ℝ (cF t) (c t))).symm.trans ?_
  refine setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [JointRepresentativeInternal.ae_coe_of_ae he] with σ hσ _
  rw [hP.2.2.1, ← hσ, ← hce]

end Breakdown.Cert
