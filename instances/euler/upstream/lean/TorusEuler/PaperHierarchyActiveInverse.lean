import TorusEuler.PaperHierarchyInverse
import TorusEuler.PaperHierarchyActiveNormBounds

/-! The transverse estimate for launch profiles defined only on the active slab. -/

open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler

open HierarchyTwistedProfile

noncomputable section

/-- The paper's spatial and phase norm weighted by the active amplitude. -/
def paperHierarchyActiveVelocityNorm (t₀ T ℓ h : ℝ) (n : ℕ) (γ : ℝ → ℝ)
    (f : ℝ → Vec3 × ℝ → Vec3) : ℝ :=
  hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
    (fun (t : Icc t₀ T) q => (γ t)⁻¹ • f t q)

/-- The paper's unweighted spatial and phase norm of the launch data. -/
def paperHierarchyLaunchValueNorm (t₀ ℓ h : ℝ) (n : ℕ)
    (f : ℝ → Vec3 × ℝ → Vec3) : ℝ :=
  hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
    (fun (t : ({t₀} : Set ℝ)) q => f t q)

set_option maxHeartbeats 4400000 in
/-- Lemma 5.3(i) for smooth twisted-periodic profiles only on ([t_0,T]).
The initial slice may be nonzero, and the solution and source need only
solve the prescribed ODE on that slab. -/
theorem exists_paper_hierarchy_inverse_of_active_profiles (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ A : ℕ, 30 ≤ A ∧ ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ freq : ℝ} {k : Vec3} {center : ℝ → Vec3}
        {hT : 0 < T} (d : ParentGeometry hT U X k),
        T ≤ 1 → 0 ≤ t₀ → t₀ < T → 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
        1 ≤ freq → ‖labelWaveVector X 0 0 k t₀‖ = freq →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (U t) a‖ ≤ D) →
        (∀ n j, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ a,
          ‖iteratedFDeriv ℝ j (U t) a‖ ≤ R n * D ^ j) →
        LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (U t) (X 0 t 0))
          (fun t => labelWaveVector X 0 0 k t) center t₀ T D →
        let h := freq ^ (-1 / 2 : ℝ);
        let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖;
        ∀ (n : ℕ) {S : Set Vec3}, IsClosed S →
          (∀ x ∈ S, ∃ z : Fin 3 → ℤ, ‖x - latticeVector z‖ ≤ 2 * ℓ) →
          ∀ V F : ℝ → Vec3 × ℝ → Vec3,
            ContDiffOn ℝ ∞ (Function.uncurry V) (Icc t₀ T ×ˢ univ) →
            ContDiffOn ℝ ∞ (Function.uncurry F) (Icc t₀ T ×ˢ univ) →
            (∀ a s, V t₀ (a, s + 1) = V t₀ (a, s)) →
            (∀ t ∈ Icc t₀ T, ∀ a s, F t (a, s + 1) = F t (a, s)) →
            (∀ a s (j : Fin 3 → ℤ),
              V t₀ (a + latticeVector j, s + ⟪k, latticeVector j⟫_ℝ) = V t₀ (a,s)) →
            (∀ t ∈ Icc t₀ T, ∀ a s (j : Fin 3 → ℤ),
              F t (a + latticeVector j, s + ⟪k, latticeVector j⟫_ℝ) = F t (a,s)) →
            (∀ x ∉ S, ∀ s, V t₀ (x,s) = 0) →
            (∀ t ∈ Icc t₀ T, ∀ x ∉ S, ∀ s, F t (x,s) = 0) →
            (∀ t ∈ Icc t₀ T, ∀ x s, ⟪d.oscillation.covector t x, V t (x,s)⟫_ℝ = 0) →
            (∀ t ∈ Icc t₀ T, ∀ x s,
              HasDerivWithinAt (fun u => V u (x,s))
                (affineWaveAmplitudeOperator (d.oscillation.strain t x) (d.oscillation.covector t x)
                    (V t (x,s)) +
                  oscillatoryTransverseProjection (d.oscillation.covector t x) (F t (x,s)))
                (Icc t₀ T) t) →
            paperHierarchyActiveVelocityNorm t₀ T ℓ h n γ V ≤
              C n * D ^ (20 : ℕ) * ((γ t₀)⁻¹ * paperHierarchyLaunchValueNorm t₀ ℓ h n V +
                paperHierarchyActiveVelocityNorm t₀ T ℓ h n γ F) := by
  obtain ⟨A, hA, hForward⟩ := exists_parentTransverseForward R hR
  obtain ⟨C, hC, hBudget⟩ := exists_parentTransverseCoefficientBudgets_with_unit_duration R hR
  refine ⟨A, hA, C, hC, ?_⟩
  intro U X T t₀ D ℓ freq k center hT d hT₁ ht₀ htT hD hℓ hRadius hf hCarrier
    hX hU hper hF hG hM hjets hc h γ n S hS hRadiusS
  let I := Icc t₀ T
  let σ := freq ^ (3 / 4 : ℝ)
  let K := Real.exp 1 * D ^ (3 : ℕ)
  have hI : I ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have ht : t₀ ∈ Icc 0 T := ⟨ht₀,htT.le⟩
  have hstart : t₀ ∈ I := ⟨le_rfl,htT.le⟩
  have hf₀ := zero_lt_one.trans_le hf
  have hγ : ContinuousOn γ I :=
    (HasDerivWithinAt.continuousOn hc.amplitude).norm.const_mul σ
  have hpos (t : ℝ) (ht' : t ∈ I) : 0 < γ t :=
    mul_pos (Real.rpow_pos_of_pos hf₀ _) (norm_pos_iff.mpr (hc.nonzero t ht').2.1)
  have hσ : 0 ≤ σ := Real.rpow_nonneg hf₀.le _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  have hEll30 : ℓ ≤ (D ^ (30 : ℕ))⁻¹ :=
    hRadius.trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ hD₁ hA))
  obtain ⟨dg,hdg,_,hg,hStable⟩ :=
    hForward hT₁ ht hD hℓ.le hRadius d hX hU hper hF hG hM hjets hc
  obtain ⟨Cgen,Ccomm,CJ,CR,CA,CB,hGen,hComm,_,hNumUnit,hJ,hR',hPA,hPB,hGenWords⟩ :=
    hBudget (h := h) hT₁ ht hD₁ hℓ hEll30 hf₀ hCarrier d hX hU hper hF hG hjets n
  obtain ⟨hJs,hRs,hJt,hRJ,hJR,_⟩ :=
    d.mean.transverseCoframe_data d.oscillation ht₀
      (fun x _ ht' => d.transverseCovector_eq (hI ht') x)
  have hDeriv (t : ℝ) (ht' : t ∈ I) : HasDerivWithinAt γ (σ * dg t) I t :=
    (hg t ht').const_mul σ
  have hCdg : ContinuousOn (fun t => σ * dg t) I := continuousOn_const.mul hdg
  have hForwardW (a : Vec3) (ha : a ∈ S) (y : ℝ → transversePlane k)
      (hy : ∀ t ∈ I, HasDerivWithinAt y
        (fixedTransverseGenerator (d.oscillation.strain t a) (d.mean.transverseLift t a)
          (d.mean.transversePullback t a) (y t)) I t)
      (t : ℝ) (ht' : t ∈ I) (u : ℝ) (hu : u ∈ Icc t T) :
      ‖y u‖ / γ u ≤ K * (‖y t‖ / γ t) :=
    HierarchyTwistedProfile.ratio_stability_const_mul (γ := fun t => ‖center t‖) hσ (hStable a (hRadiusS a ha) y hy t ht' u hu)
  have hCJ : 0 ≤ CJ := hJ.1
  have hCR : 0 ≤ CR := hR'.1
  have hCA : 0 ≤ CA := hPA.1
  have hCB : 0 ≤ CB := hPB.1
  have hComm₀ : 0 ≤ Ccomm := (by positivity : 0 ≤ K * (T - t₀) * Cgen).trans hComm
  have hVC : 0 ≤ transverseVelocityWordConstant n 1 K Ccomm CJ CR := by
    have hword := linearODEWordFactor_nonneg hComm₀ n
    unfold transverseVelocityWordConstant
    positivity
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  have hCountV : count * transverseVelocityWordConstant n 1 K Ccomm CJ CR ≤ C n * D ^ 20 := by
    unfold transverseSolveNormConstant at hNumUnit
    dsimp only at hNumUnit
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (Nat.cast_nonneg _)).trans hNumUnit
  intro V F hVreg hFreg hVphase hFphase hVtwist hFtwist hInit hForce hTrans hODE
  let I₀ := (γ t₀)⁻¹ * paperHierarchyLaunchValueNorm t₀ ℓ h n V
  let F₀ := paperHierarchyActiveVelocityNorm t₀ T ℓ h n γ F
  let S₀ : Set ℝ := {t₀}
  have hS₀ : S₀ ⊆ I := singleton_subset_iff.mpr hstart
  have hV₀ : ContDiff ℝ ∞ (V t₀) :=
    contDiffOn_univ.mp (hVreg.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun q _ => ⟨hstart, mem_univ q⟩))
  have hVconst : ContDiffOn ℝ ∞ (Function.uncurry (fun (_ : ℝ) => V t₀)) (I ×ˢ univ) :=
    hV₀.comp_contDiffOn contDiffOn_snd
  have hInitFin (w : List (Fin 4)) (_ : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (fun (t : S₀) p => V t p)) := by
    have hb := paperHierarchyActiveWord_bddAbove (ℓ := ℓ) (h := h) (k := k)
      htT hVconst (fun _ _ => hVphase) (fun _ _ => hVtwist) hS₀ (fun _ => 1)
      (fun _ _ => (norm_one : ‖(1 : ℝ)‖ = 1).le) w
    have hSlice : (fun (t : S₀) p => V t p) = fun (_ : S₀) p => V t₀ p := by
      funext t
      have ht' : (t : ℝ) = t₀ := mem_singleton_iff.mp t.property
      change V (t : ℝ) = V t₀
      rw [ht']
    rw [hSlice]
    simpa only [one_smul] using hb
  have hInitRaw : HierarchyRelayWordBound ℓ h n (paperHierarchyLaunchValueNorm t₀ ℓ h n V)
      (fun (t : S₀) p => V t p) :=
    hierarchyRelayWordBound_of_finiteNorm hInitFin
  have hInitB : HierarchyRelayWordBound ℓ h n I₀
      (fun (_ : I) p => (γ t₀)⁻¹ • V t₀ p) := by
    have hg₀ : 0 ≤ (γ t₀)⁻¹ := inv_nonneg.mpr (hpos t₀ hstart).le
    refine ⟨mul_nonneg hg₀ hInitRaw.1, fun w hw _ q => ?_⟩
    rw [phaseOperatorWord_const_smul (D := hierarchyMixedDirection ℓ h) (fun _ => contDiff_const)
      hV₀, norm_smul_of_nonneg hg₀]
    exact mul_le_mul_of_nonneg_left (hInitRaw.2 w hw ⟨t₀, mem_singleton _⟩ q) hg₀
  obtain ⟨B, hB⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT.le) hγ hpos
  have hForceB : HierarchyRelayWordBound ℓ h n F₀ (fun (t : I) p => (γ t)⁻¹ • F t p) :=
    hierarchyRelayWordBound_of_finiteNorm fun w _ =>
      paperHierarchyActiveWord_bddAbove (ℓ := ℓ) (h := h) (k := k)
        htT hFreg hFphase hFtwist (Subset.rfl : I ⊆ I) (fun t => (γ t)⁻¹) hB w
  have hMreg := d.oscillation.strain_smooth.mono (prod_mono hI (Subset.rfl : (univ : Set Vec3) ⊆ univ))
  let q (t : ℝ) (y : Vec3 × ℝ) := oscillatoryPressureSlope (d.oscillation.strain t y.1)
    (d.oscillation.covector t y.1) (F t y) (V t y)
  have hEq (y : Vec3 × ℝ) (t : ℝ) (ht' : t ∈ I) :
      HasDerivWithinAt (fun u => V u y)
        (F t y - d.oscillation.strain t y.1 (V t y) - q t y • d.oscillation.covector t y.1) I t := by
    simpa only [q, ← affineWaveAmplitudeOperator_add_transverseProjection] using hODE t ht' y.1 y.2
  have hv := oscillatoryVelocity_weightedWordBound_of_initial (S := S ×ˢ (univ : Set ℝ))
    n htT hK hGen hComm (hS.prod isClosed_univ) hJs hRs hMreg hFreg hVreg
    (fun y hy => hInit y.1 (fun ha => hy ⟨ha,mem_univ _⟩) y.2)
    hJt hRJ hJR hEq (fun y t ht' => hTrans t ht' y.1 y.2)
    (fun y hy t ht' => hForce t ht' y.1 (fun ha => hy ⟨ha,mem_univ _⟩) y.2)
    hpos hDeriv hCdg hJ hR' hInitB hForceB
    (fun y hy => hForwardW y.1 hy.1) (fun w hw hn y _ t ht' => hGenWords w hw hn t ht' y)
  have hNorm := hierarchyFiniteWordNorm_sup_le hv.1 hv.2
  have hRate := HierarchyTwistedProfile.transverseVelocityWordConstant_le_unit
    (n := n) (B := I₀) (H := F₀) (r := T - t₀) (K := K)
    (by linarith) hK hComm₀ hCJ hCR hForceB.1
  calc
    _ ≤ count * _ := hNorm
    _ ≤ count * (transverseVelocityWordConstant n 1 K Ccomm CJ CR * (I₀ + F₀)) :=
      mul_le_mul_of_nonneg_left hRate (Nat.cast_nonneg _)
    _ = (count * transverseVelocityWordConstant n 1 K Ccomm CJ CR) * (I₀ + F₀) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hCountV (add_nonneg hInitB.1 hForceB.1)

end

end TorusEuler
