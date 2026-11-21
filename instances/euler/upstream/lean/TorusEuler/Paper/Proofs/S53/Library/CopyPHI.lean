import TorusEuler.PaperHierarchyInverse
import TorusEuler.Paper.Proofs.S53.Library.Leaves
import TorusEuler.Paper.Proofs.S53.Library.Leaf51
import TorusEuler.Paper.Proofs.S53.Library.CopyConstHTN
import TorusEuler.Paper.Proofs.S53.Library.CopyConstPHI
import TorusEuler.Paper.Proofs.S53.Library.D2Bridge
import TorusEuler.Paper.Proofs.S53.Library.D2Coframe
import TorusEuler.Paper.Proofs.S53.Library.CopyLAC
import TorusEuler.Paper.Proofs.S53.Library.CopyLACaux
import TorusEuler.Paper.Proofs.S53.Library.CopyODEaux
import TorusEuler.Paper.Proofs.S53.Library.CopyODE
import TorusEuler.Paper.Proofs.S53.Library.CopyConstHTN
import TorusEuler.Paper.Proofs.S53.Library.CopyConstHTB
import TorusEuler.Paper.Proofs.S53.Library.CopyConstPHI
import TorusEuler.Paper.Proofs.S53.Library.CopySDB
import TorusEuler.Paper.Proofs.S53.Library.CopyPSJ
import TorusEuler.Paper.Proofs.S53.Library.CopyHTN
import TorusEuler.Paper.Proofs.S53.Library.CopyHTB

/-!
# S53 library: Lemma 5.3 chain: the transverse inverse and the leading profile

Generated copy (script `s53tools/mkcopy.py`) of the declarations exists_paper_hierarchy_inverse, exists_paper_hierarchy_leading, launch_wordBound, weighted_rawNorm_le_of_scaledJets of
`TorusEuler/PaperHierarchyInverse.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile

open TorusEuler.HierarchyTwistedProfile
noncomputable section

omit [TorusEuler.Paper.Lib.S53.Leaves] in
set_option maxHeartbeats 2000000 in
/-- Copy of the library lemma `TorusEuler.launch_wordBound` (glue), placed in `Paper.Lib.S53`. -/
theorem launch_wordBound {T t₀ : ℝ} {k : Vec3} (hT : 0 < T) (ht₀ : t₀ ∈ Icc 0 T)
    {γ : ℝ → ℝ} (hγ : 0 < γ t₀) (ℓ h : ℝ) (n : ℕ) (V : HierarchyTwistedProfile T k Vec3) :
    HierarchyRelayWordBound ℓ h n ((γ t₀)⁻¹ * hierarchyLaunchSeminorm hT ht₀ ℓ h n V)
      (fun (_ : Icc t₀ T) p => (γ t₀)⁻¹ • V.val.val.val (t₀,p)) := by
  have hS : ({t₀} : Set ℝ) ⊆ Icc 0 T := singleton_subset_iff.mpr ht₀
  have h₁ : ∀ t ∈ ({t₀} : Set ℝ), ‖(1 : ℝ)‖ ≤ 1 := by simp
  have hNorm : HierarchyRelayWordBound ℓ h n (hierarchyLaunchSeminorm hT ht₀ ℓ h n V)
      (weightedSlices ({t₀} : Set ℝ) (fun _ => 1) V) := by
    unfold hierarchyLaunchSeminorm
    rw [boundedWeightSeminorm_apply]
    refine hierarchyRelayWordBound_of_finiteNorm
      (f := weightedSlices ({t₀} : Set ℝ) (fun _ => 1) V) (ℓ := ℓ) (h := h) (n := n) ?_
    intro w _
    change BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
      (fun (t : ({t₀} : Set ℝ)) x => (1 : ℝ) • V.val.val.val ((t : ℝ), x)))
    exact hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w V hS (fun _ => 1) h₁
  have hV : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => V.val.val.val (t₀,p)) :=
    HierarchySmoothProfile.contDiff_labelPhase_slice V.val.val ht₀
  refine ⟨mul_nonneg (inv_nonneg.mpr hγ.le) (apply_nonneg _ _), fun w hw _ p => ?_⟩
  have hb := hNorm.2 w hw ⟨t₀, mem_singleton _⟩ p
  change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w
    (fun q => (1 : ℝ) • V.val.val.val (t₀,q)) p‖ ≤ _ at hb
  simp only [one_smul] at hb
  rw [phaseOperatorWord_const_smul (D := hierarchyMixedDirection ℓ h) (fun _ => contDiff_const) hV, norm_smul_of_nonneg (inv_nonneg.mpr hγ.le)]
  exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hγ.le)

set_option maxHeartbeats 4000000 in
/-- Lemma 5.3(i)–(ii) (cc:uf:tower:lem:inverse) for arbitrary smooth
supported launch data and for the selected zero-start transverse solve.
The frequency-weighted active seminorms are the actual Appendix D norms. -/
theorem exists_paper_hierarchy_inverse (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ A : ℕ, 30 ≤ A ∧ ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ freq : ℝ} {k : Vec3} {center : ℝ → Vec3}
        {hT : 0 < T} (d : ParentGeometry hT U X k),
        T ≤ 1 → (ht₀ : 0 ≤ t₀) → (htT : t₀ < T) → 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
        (hf : 1 ≤ freq) → ‖labelWaveVector X 0 0 k t₀‖ = freq →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (U t) a‖ ≤ D) →
        Leaf2 R U X T D k freq →
        (hc : LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (U t) (X 0 t 0))
          (fun t => labelWaveVector X 0 0 k t) center t₀ T D) →
        let h := freq ^ (-1 / 2 : ℝ);
        let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖;
        let hγ := (HasDerivWithinAt.continuousOn hc.amplitude).norm.const_mul (freq ^ (3 / 4 : ℝ));
        let hpos := fun t ht => mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hf) _)
          (norm_pos_iff.mpr (hc.nonzero t ht).2.1);
        ∀ (n : ℕ) {S : Set Vec3}, IsClosed S →
          (∀ x ∈ S, ∃ z : Fin 3 → ℤ, ‖x - latticeVector z‖ ≤ 2 * ℓ) →
          let W := amplitudeSeminorm (E := Vec3) (k := k) False ℓ h n hT ht₀ htT.le γ hγ hpos;
          let P := amplitudeSeminorm (E := ℝ) (k := k) False ℓ h n hT ht₀ htT.le γ hγ hpos;
          let N := hierarchyLaunchSeminorm (k := k) hT ⟨ht₀,htT.le⟩ ℓ h n;
          (∀ V F : HierarchyTwistedProfile T k Vec3,
            (∀ x ∉ S, ∀ s, V.val.val.val (t₀,x,s) = 0) →
            (∀ t ∈ Icc t₀ T, ∀ x ∉ S, ∀ s, F.val.val.val (t,x,s) = 0) →
            (∀ t ∈ Icc t₀ T, ∀ x s,
              ⟪d.oscillation.covector t x, V.val.val.val (t,x,s)⟫_ℝ = 0) →
            (∀ t ∈ Icc t₀ T, ∀ x s,
              HasDerivWithinAt (fun u => V.val.val.val (u,x,s))
                (affineWaveAmplitudeOperator (d.oscillation.strain t x) (d.oscillation.covector t x)
                  (V.val.val.val (t,x,s)) +
                  oscillatoryTransverseProjection (d.oscillation.covector t x) (F.val.val.val (t,x,s)))
                (Icc t₀ T) t) →
            W V ≤ C n * D ^ (20 : ℕ) * ((γ t₀)⁻¹ * N V + W F)) ∧
          (∀ F : HierarchyTwistedProfile T k Vec3,
            (hMean : (twistedHierarchyOperators hT d.inverse d.strain d.covector).average F = 0) →
            (∀ t ∈ Icc 0 T, ∀ x s, t < t₀ ∨ x ∉ S → F.val.val.val (t,x,s) = 0) →
            let sol := solveTransverse hT d.inverse d.strain d.covector d.oscillation F hMean
            W sol.output.V + freq * P sol.output.p ≤ C n * D ^ (20 : ℕ) * W F) := by
  obtain ⟨A, hA, hForward⟩ := exists_parentTransverseForward R hR
  obtain ⟨C, hC, hBudget⟩ := exists_parentTransverseCoefficientBudgets_with_unit_duration R hR
  refine ⟨A, hA, C, hC, ?_⟩
  intro U X T t₀ D ℓ freq k center hT d hT₁ ht₀ htT hD hℓ hRadius hf hCarrier
    hX hU hper hF hG hM hjets hc h γ hγ hpos n S hS hRadiusS W P N
  let I := Icc t₀ T
  let σ := freq ^ (3 / 4 : ℝ)
  let K := Real.exp 1 * D ^ (3 : ℕ)
  have hI : I ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have ht : t₀ ∈ Icc 0 T := ⟨ht₀,htT.le⟩
  have hstart : t₀ ∈ I := ⟨le_rfl,htT.le⟩
  have hf₀ := zero_lt_one.trans_le hf
  have hσ : 0 ≤ σ := Real.rpow_nonneg hf₀.le _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  have hEll30 : ℓ ≤ (D ^ (30 : ℕ))⁻¹ :=
    hRadius.trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ hD₁ hA))
  obtain ⟨dg,hdg,_,hg,hStable⟩ :=
    hForward hT₁ ht hD hℓ.le hRadius d hX hU hper hF hG hM (hCarrier.symm ▸ Leaf2.toLeaf hR hjets) hc
  obtain ⟨Cgen,Ccomm,CJ,CR,CA,CB,hGen,hComm,hNum,hNumUnit,hJ,hR',hPA,hPB,hGenWords⟩ :=
    hBudget (h := h) hT₁ ht hD₁ hℓ hEll30 hf₀ hCarrier d hX hU hper hF hG hjets n
  obtain ⟨hJs,hRs,hJt,hRJ,hJR,hκ⟩ :=
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
    ratio_stability_const_mul (γ := fun t => ‖center t‖) hσ (hStable a (hRadiusS a ha) y hy t ht' u hu)
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
  constructor
  · intro V F hInit hForce hTrans hODE
    let I₀ := (γ t₀)⁻¹ * N V
    let F₀ := W F
    have hinitB := launch_wordBound (γ := γ) hT ht (hpos t₀ hstart) ℓ h n V
    have hforceB := wordBound_of_amplitudeSeminorm hT ht₀ htT.le hγ hpos ℓ h n F
    have hMreg := d.oscillation.strain_smooth.mono (prod_mono hI (Subset.rfl : (univ : Set Vec3) ⊆ univ))
    let vel (t : ℝ) (q : Vec3 × ℝ) := V.val.val.val (t,q)
    let frc (t : ℝ) (q : Vec3 × ℝ) := F.val.val.val (t,q)
    let q (t : ℝ) (y : Vec3 × ℝ) := oscillatoryPressureSlope (d.oscillation.strain t y.1)
      (d.oscillation.covector t y.1) (frc t y) (vel t y)
    have hVreg : ContDiffOn ℝ ∞ (Function.uncurry vel) (I ×ˢ univ) :=
      (HierarchySmoothProfile.smooth V.val.val).mono (prod_mono hI le_rfl)
    have hFreg : ContDiffOn ℝ ∞ (Function.uncurry frc) (I ×ˢ univ) :=
      (HierarchySmoothProfile.smooth F.val.val).mono (prod_mono hI le_rfl)
    have hEq (y : Vec3 × ℝ) (t : ℝ) (ht' : t ∈ I) :
        HasDerivWithinAt (fun u => vel u y)
          (frc t y - d.oscillation.strain t y.1 (vel t y) - q t y • d.oscillation.covector t y.1) I t := by
      simpa only [q, frc, vel, ← affineWaveAmplitudeOperator_add_transverseProjection] using hODE t ht' y.1 y.2
    have hb := oscillatoryVelocity_weightedWordBound_of_initial (S := S ×ˢ (univ : Set ℝ))
      n htT hK hGen hComm (hS.prod isClosed_univ) hJs hRs hMreg hFreg hVreg
      (fun y hy => hInit y.1 (fun ha => hy ⟨ha,mem_univ _⟩) y.2)
      hJt hRJ hJR hEq (fun y t ht' => hTrans t ht' y.1 y.2)
      (fun y hy t ht' => hForce t ht' y.1 (fun ha => hy ⟨ha,mem_univ _⟩) y.2)
      hpos hDeriv hCdg hJ hR' hinitB hforceB
      (fun y hy => hForwardW y.1 hy.1) (fun w hw hn y hy t ht' => hGenWords w hw hn t ht' y)
    have hW := amplitudeSeminorm_le_of_wordBound hT ht₀ htT.le hγ hpos (f := V) hb
    refine hW.trans ?_
    have hRate := transverseVelocityWordConstant_le_unit (n := n) (B := I₀) (H := F₀)
      (r := T - t₀) (K := K) (by linarith) hK hComm₀ hCJ hCR (apply_nonneg W F)
    calc
      _ ≤ count * (transverseVelocityWordConstant n 1 K Ccomm CJ CR * (I₀ + F₀)) :=
        mul_le_mul_of_nonneg_left hRate (Nat.cast_nonneg _)
      _ = (count * transverseVelocityWordConstant n 1 K Ccomm CJ CR) * (I₀ + F₀) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCountV
        (add_nonneg (mul_nonneg (inv_nonneg.mpr (hpos _ hstart).le) (apply_nonneg N _)) (apply_nonneg W F))
  · intro F hMean hForce sol
    have hhpos : 0 < h := Real.rpow_pos_of_pos hf₀ _
    have hEst := TransverseResult.norm_bound sol d.oscillation hMean ht₀ htT hS hForce hγ hpos hDeriv hCdg
      hJs hRs hJt hRJ hJR hf₀ hℓ hhpos hK hGen hComm hκ hJ hR' hPA hPB
      (fun y hy => hForwardW y.1 hy) (fun w hw hn y _ t ht' => hGenWords w hw hn t ht' y)
    exact hEst.trans (mul_le_mul_of_nonneg_right hNum (apply_nonneg W _))

end

end TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile

namespace TorusEuler.Paper.Lib.S53.LocalizedAmplitude

open TorusEuler.LocalizedAmplitude
noncomputable section

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- Copy of the library lemma `TorusEuler.weighted_rawNorm_le_of_scaledJets` (glue), placed in `Paper.Lib.S53`. -/
theorem weighted_rawNorm_le_of_scaledJets
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t₀ T ℓ h c B : ℝ} {γ : ℝ → ℝ} {n : ℕ} {f : ℝ → Vec3 → ℝ → E}
    (hℓ : ℓ ≠ 0) (hh : h ≠ 0) (hc : 0 < c) (hB : 0 ≤ B)
    (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hf : ∀ t ∈ Icc t₀ T, ContDiff ℝ ∞ (Function.uncurry (f t)))
    (hJet : ∀ t ∈ Icc t₀ T, PhaseJetBound n (γ t * B)
      (scaledPhaseProfile ℓ h (fun x s => c • f t x s))) :
    c * hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun (t : Icc t₀ T) (p : Vec3 × ℝ) => (γ t)⁻¹ • f t p.1 p.2) ≤
      ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ) * B := by
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  have hNorm (w : List (Fin 4)) (hw : w ∈ hierarchyAdmissibleWords (Fin 4) n)
      (t : Icc t₀ T) (x : Vec3 × ℝ) :
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w
        (fun p => (γ t)⁻¹ • f t p.1 p.2) x‖ ≤ B / c := by
    have ht := hγ t t.property
    have hs := norm_hierarchyMixedWord_le_of_scaledJetBound
      ((hf t t.property).const_smul c) hℓ hh (hJet t t.property)
      w (mem_hierarchyAdmissibleWords.mp hw).1 x
    change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w
      (fun p => c • f t p.1 p.2) x‖ ≤ _ at hs
    have hf' : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => f t p.1 p.2) := hf t t.property
    rw [phaseOperatorWord_const_smul (D := hierarchyMixedDirection ℓ h)
      (fun _ => contDiff_const) hf' c w x, norm_smul_of_nonneg hc.le] at hs
    rw [phaseOperatorWord_const_smul (D := hierarchyMixedDirection ℓ h)
      (fun _ => contDiff_const) hf' (γ t)⁻¹ w x, norm_smul_of_nonneg (inv_nonneg.mpr ht.le)]
    apply (le_div_iff₀ hc).2
    calc
      _ = (γ t)⁻¹ * (c * ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w
          (fun p => f t p.1 p.2) x‖) := by ring
      _ ≤ (γ t)⁻¹ * (γ t * B) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr ht.le)
      _ = B := by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  have h := hierarchyFiniteWordNorm_sup_le (div_nonneg hB hc.le) hNorm
  calc
    _ ≤ c * (count * (B / c)) := mul_le_mul_of_nonneg_left h hc.le
    _ = count * B * (c * c⁻¹) := by rw [div_eq_mul_inv]; ring
    _ = _ := by rw [mul_inv_cancel₀ hc.ne', mul_one]

set_option maxHeartbeats 2300000 in
/-- Lemma 5.3(iii) for the unswitched leading velocity and its normalized
primitive pressure on the active slab. The norm is taken in the independent
label and phase, before taking the physical graph. -/
theorem exists_paper_hierarchy_leading (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ A : ℕ, 30 ≤ A ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ Cseed freq : ℝ} {k : Vec3} {center : ℝ → Vec3},
        0 ≤ t₀ → t₀ < T → T ≤ 1 → 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
        1 ≤ freq → ‖labelWaveVector X 0 0 k t₀‖ = freq →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        Leaf2 R U X T D k freq →
        let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a);
        let κ (t : ℝ) (a : Vec3) := labelWaveVector X 0 a k t;
        CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D →
        ∀ (w : SeedOn M κ center t₀ T ℓ D Cseed),
        let h := freq ^ (-1 / 2 : ℝ);
        w.HierarchyRegularity 0 h →
        let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖;
        hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
            (fun (t : Icc t₀ T) (p : Vec3 × ℝ) => (γ t)⁻¹ • w.leading h t p.1 p.2) +
          freq * hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
            (fun (t : Icc t₀ T) (p : Vec3 × ℝ) => (γ t)⁻¹ • w.leadingPressure h t p.1 p.2) ≤
          C * D ^ (20 : ℕ) * freq ^ (-5 / 4 : ℝ) := by
  obtain ⟨A,hA,hRaw⟩ := exists_parent_seed_leadingScaledJetBounds R hR
  refine ⟨A,hA,fun n => ?_⟩
  obtain ⟨C,hC,hBound⟩ := hRaw n
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  refine ⟨2 * count * C, by positivity, ?_⟩
  intro U X T t₀ D ℓ Cseed freq k center ht₀ htT hT₁ hD hℓ hRadius hf hCarrier hX hU hper hF hG hjets
    M κ hCenter w h reg γ
  let B := C * D ^ (20 : ℕ) * freq ^ (-5 / 4 : ℝ)
  have hf₀ := zero_lt_one.trans_le hf
  have hγ (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < γ t :=
    mul_pos (Real.rpow_pos_of_pos hf₀ _) (norm_pos_iff.mpr (hCenter.nonzero t ht).2.1)
  have hB : 0 ≤ B := by unfold B; positivity
  have hslice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec3 → ℝ → E}
      (hs : ContDiffOn ℝ ∞ (fun x : ℝ × Vec3 × ℝ => f x.1 x.2.1 x.2.2) (Icc t₀ T ×ˢ univ))
      (t : ℝ) (ht : t ∈ Icc t₀ T) : ContDiff ℝ ∞ (Function.uncurry (f t)) :=
    contDiffOn_univ.mp (hs.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hV := hslice (w.contDiffOn_leading hℓ reg.phase_pos reg.phase_le_one reg.amplitude_smooth)
  have hP := hslice (w.contDiffOn_leadingPressure hℓ reg.phase_pos reg.phase_le_one reg.strain_smooth
    reg.covector_smooth reg.covector_nonzero reg.amplitude_smooth)
  have hj (t : ℝ) (ht : t ∈ Icc t₀ T) :=
    hBound ht₀ htT hT₁ hD hℓ hRadius hf hCarrier hX hU hper hF hG hjets hCenter w
      (χ := 1) (by norm_num) t ht
  have hVel := weighted_rawNorm_le_of_scaledJets hℓ.ne' reg.phase_pos.ne' (c := 1) zero_lt_one hB hγ hV
    (fun t ht => (hj t ht).1)
  have hPressure := weighted_rawNorm_le_of_scaledJets hℓ.ne' reg.phase_pos.ne' hf₀ hB hγ hP
    (fun t ht => by simpa only [smul_eq_mul, one_mul] using (hj t ht).2)
  simp only [one_mul] at hVel
  exact (add_le_add hVel hPressure).trans_eq (by unfold B; ring)

end
end TorusEuler.Paper.Lib.S53.LocalizedAmplitude

