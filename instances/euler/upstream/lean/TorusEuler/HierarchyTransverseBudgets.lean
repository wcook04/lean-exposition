import TorusEuler.HierarchyTransverseNorms
import TorusEuler.SeedDerivativeBudgets
import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.PhysicalWaveEnvelopeSupport

/-! Forward stability and coefficient budgets for the physical transverse hierarchy. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "Plane" => transversePlane k

/-- The generator on the fixed launch plane is periodic in the label. -/
theorem MeanCoefficients.transverseGenerator_periodic {G M : MP} {κ : VP}
    (d : MeanCoefficients G M) (osc : TransverseCoefficients M κ)
    (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (fun a =>
      fixedTransverseGenerator (osc.strain t a) (d.transverseLift t a) (d.transversePullback t a)) := by
  intro m a
  have h : toUnitTorus (a + latticeVector m) = toUnitTorus a :=
    (toUnitTorus_eq_iff _ _).mpr ⟨m, rfl⟩
  simp only [MeanCoefficients.transverseLift, MeanCoefficients.transversePullback,
    osc.strain_periodic t ht m a, h]

set_option maxHeartbeats 1200000 in
/-- The physical center estimate yields the fixed-plane forward bound at every
label within the specified radius of a lattice translate. -/
theorem MeanCoefficients.transverseForward_of_center {G M : MP} {κ : VP}
    (d : MeanCoefficients G M) (osc : TransverseCoefficients M κ)
    {t₀ D ℓ L : ℝ} {center : ℝ → Vec3} (ht₀ : 0 ≤ t₀) (hT₁ : T ≤ 1) (hD : 2 ≤ D)
    (hκ : ∀ a t, t ∈ Icc t₀ T → osc.covector t a = (d.inverse (t, toUnitTorus a)).adjoint k)
    (hCenter : LocalizedAmplitude.CenterWaveOn (fun t => osc.strain t 0)
      (fun t => osc.covector t 0) center t₀ T D)
    (hF : ∀ a t, t ∈ Icc t₀ T → ‖d.deformation (t, toUnitTorus a)‖ ≤ D)
    (hG : ∀ a t, t ∈ Icc t₀ T → ‖d.inverse (t, toUnitTorus a)‖ ≤ D)
    (hM : ∀ a t, t ∈ Icc t₀ T → ‖osc.strain t a‖ ≤ D)
    (hL : 0 ≤ L) (hSmall : D ^ 3 * LocalizedAmplitude.generatorLabelSlope D L L L L * (2 * ℓ) ≤ 1)
    (hLip : ∀ a t, t ∈ Icc t₀ T →
      ‖d.deformation (t, toUnitTorus a) - d.deformation (t, toUnitTorus 0)‖ ≤ L * ‖a‖ ∧
      ‖d.inverse (t, toUnitTorus a) - d.inverse (t, toUnitTorus 0)‖ ≤ L * ‖a‖ ∧
      ‖osc.strain t a - osc.strain t 0‖ ≤ L * ‖a‖ ∧
      ‖oscillatoryTransverseProjection (osc.covector t a) -
        oscillatoryTransverseProjection (osc.covector t 0)‖ ≤ L * ‖a‖) :
    ∃ dg : ℝ → ℝ, ContinuousOn dg (Icc t₀ T) ∧
      (∀ t ∈ Icc t₀ T, 0 < ‖center t‖) ∧
      (∀ t ∈ Icc t₀ T, HasDerivWithinAt (fun u => ‖center u‖) (dg t) (Icc t₀ T) t) ∧
      ∀ a : Vec3, (∃ m : Fin 3 → ℤ, ‖a - latticeVector m‖ ≤ 2 * ℓ) →
        ∀ x : ℝ → Plane,
          (∀ t ∈ Icc t₀ T, HasDerivWithinAt x
            (fixedTransverseGenerator (osc.strain t a) (d.transverseLift t a)
              (d.transversePullback t a) (x t)) (Icc t₀ T) t) →
          ∀ u ∈ Icc t₀ T, ∀ v ∈ Icc u T,
            ‖x v‖ / ‖center v‖ ≤ (Real.exp 1 * D ^ 3) * (‖x u‖ / ‖center u‖) := by
  let I := Icc t₀ T
  let A (t : ℝ) (a : Vec3) :=
    fixedTransverseGenerator (osc.strain t a) (d.transverseLift t a) (d.transversePullback t a)
  have hD₀ : 0 ≤ D := by linarith
  have hD₁ : 0 < D := by linarith
  have hI : I ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hslice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec3 → E}
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ (univ : Set Vec3))) (a : Vec3) :
      ContinuousOn (fun t => f t a) I :=
    hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht, mem_univ a⟩)
  obtain ⟨hJc, hRc, hJt, hRJ, hJR, hn⟩ := d.transverseCoframe_data osc ht₀ hκ
  have hMc := hslice (osc.strain_smooth.mono (prod_mono hI le_rfl))
  have hκc := hslice (osc.covector_smooth.mono (prod_mono hI le_rfl))
  have hAc (a : Vec3) : ContinuousOn (fun t => A t a) I :=
    continuousOn_fixedTransverseGenerator (hMc a) (hslice hJc a) (hslice hRc a)
  have hpos (t : ℝ) (ht : t ∈ I) : 0 < ‖center t‖ :=
    norm_pos_iff.mpr (hCenter.nonzero t ht).2.1
  have hPhys := continuousOn_affineWaveAmplitudeOperator (hMc 0) (hκc 0) (fun t ht => hn 0 t ht)
  obtain ⟨dg, hdg, hg⟩ := LocalizedAmplitude.norm_hasContinuous_derivative hCenter.amplitude
    (hPhys.clm_apply (HasDerivWithinAt.continuousOn hCenter.amplitude))
    (fun t ht => (hCenter.nonzero t ht).2.1)
  have hStable (z : ℝ → Plane)
      (hz : ∀ t ∈ I, HasDerivWithinAt z (A t 0 (z t)) I t)
      (u : ℝ) (hu : u ∈ I) (v : ℝ) (hv : v ∈ Icc u T) :
      ‖z v‖ / ‖center v‖ ≤ D ^ 3 * (‖z u‖ / ‖center u‖) := by
    have hv' : v ∈ I := ⟨hu.1.trans hv.1, hv.2⟩
    have hs := weighted_fixedTransverse_forward hD₀ hD₀ (hn 0) hpos (hRJ 0) (hJR 0) (hJt 0)
      (fun t ht => (LocalizedAmplitude.norm_coframeLift_le k _).trans (hF 0 t ht))
      (fun t ht => (LocalizedAmplitude.norm_coframePullback_le k _).trans (hG 0 t ht))
      hCenter.stability z hz hu hv' hv.1
    simpa only [show D ^ 3 = D * D * D by ring] using hs
  refine ⟨dg, hdg, hpos, hg, ?_⟩
  intro a ha x hx u hu v hv
  obtain ⟨m, hm⟩ := ha
  have hChange (t : ℝ) (ht : t ∈ I) : ‖A t a - A t 0‖ ≤ (D ^ 3)⁻¹ := by
    let b := a - latticeVector m
    have hb : A t a = A t b := by
      have hper := d.transverseGenerator_periodic osc t (hI ht) m b
      simpa only [b, sub_add_cancel] using hper
    obtain ⟨hFb, hGb, hMb, hPb⟩ := hLip b t ht
    rw [hκ b t ht, hκ 0 t ht] at hPb
    have h := LocalizedAmplitude.norm_coframe_fixedGenerator_sub_le k hD₀
      (hF b t ht) (hG 0 t ht) (hM b t ht) (hM 0 t ht) hFb hGb hMb hPb
    rw [hb]
    refine h.trans ((mul_le_mul_of_nonneg_left hm ?_).trans ?_)
    · unfold LocalizedAmplitude.generatorLabelSlope
      positivity
    · rw [← one_div]
      apply (le_div_iff₀ (pow_pos hD₁ 3)).2
      calc
        _ = D ^ 3 * LocalizedAmplitude.generatorLabelSlope D L L L L * (2 * ℓ) := by ring
        _ ≤ _ := hSmall
  exact weighted_near_label_stability_Icc (pow_pos hD₁ 3) (by linarith) (hAc 0) (hAc a)
    hChange hpos hg hdg hStable x hx hu hv

variable {U : Velocity} {X : ℝ → Velocity} {hT : 0 < T}

/-- The canonical coefficient values agree with the forward strain and
inverse-transpose covector of the parent flow. -/
theorem ParentGeometry.transverse_values (d : ParentGeometry hT U X k) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) :
    d.mean.inverse (t, toUnitTorus a) = fderiv ℝ (X t 0) (X 0 t a) ∧
    d.oscillation.strain t a = fderiv ℝ (U t) (X 0 t a) ∧
    d.oscillation.covector t a = labelWaveVector X 0 a k t := by
  have hx : (t,a,(0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  exact ⟨(d.mean.inverse_value _ hx).symm.trans (d.inverse_value _ hx),
    (d.oscillation.strain_value _ hx).symm.trans (d.strain_value _ hx),
    (d.oscillation.covector_value _ hx).symm.trans (d.covector_value _ hx)⟩

/-- The canonical covector is the inverse-transpose image of the launch
covector. -/
theorem ParentGeometry.transverseCovector_eq (d : ParentGeometry hT U X k) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) :
    d.oscillation.covector t a = (d.mean.inverse (t, toUnitTorus a)).adjoint k := by
  rw [(d.transverse_values ht a).2.2, (d.transverse_values ht a).1]
  rfl

set_option maxHeartbeats 1400000 in
/-- The parent deformation and velocity bounds determine a radius exponent
for the selected fixed-plane forward propagator. -/
theorem exists_parentTransverseForward (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n) :
    ∃ A : ℕ, 30 ≤ A ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ : ℝ} {k : Vec3} {b : ℝ → Vec3}
        {hT : 0 < T}, T ≤ 1 → t₀ ∈ Icc 0 T → 2 ≤ D → 0 ≤ ℓ → ℓ ≤ (D ^ A)⁻¹ →
        (g : ParentGeometry hT U X k) →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (U t) a‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ a,
          ‖iteratedFDeriv ℝ j (U t) a‖ ≤ V n * D ^ j) →
        LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (U t) (X 0 t 0))
          (fun t => labelWaveVector X 0 0 k t) b t₀ T D →
        ∃ dg : ℝ → ℝ, ContinuousOn dg (Icc t₀ T) ∧
          (∀ t ∈ Icc t₀ T, 0 < ‖b t‖) ∧
          (∀ t ∈ Icc t₀ T, HasDerivWithinAt (fun u => ‖b u‖) (dg t) (Icc t₀ T) t) ∧
          ∀ a : Vec3, (∃ m : Fin 3 → ℤ, ‖a - latticeVector m‖ ≤ 2 * ℓ) →
            ∀ x : ℝ → transversePlane k,
              (∀ t ∈ Icc t₀ T, HasDerivWithinAt x
                (fixedTransverseGenerator (g.oscillation.strain t a) (g.mean.transverseLift t a)
                  (g.mean.transversePullback t a) (x t)) (Icc t₀ T) t) →
              ∀ u ∈ Icc t₀ T, ∀ v ∈ Icc u T,
                ‖x v‖ / ‖b v‖ ≤ (Real.exp 1 * D ^ 3) * (‖x u‖ / ‖b u‖) := by
  obtain ⟨C, hC, hLip⟩ := exists_parent_coefficient_label_lipschitz V hV
  obtain ⟨A, _, hRadius⟩ := LocalizedAmplitude.exists_common_envelope_exponent C hC
  refine ⟨max A 30, le_max_right _ _, ?_⟩
  intro U X T t₀ D ℓ k b hT hT₁ ht₀ hD hℓ hEll d hX hU hper hF hG hM hUjet hCenter
  let I := Icc t₀ T
  let L := C * D ^ 24
  have hD₁ : 1 ≤ D := by linarith
  have hsub : I ⊆ Icc 0 T := Icc_subset_Icc_left ht₀.1
  have hL₀ : 0 ≤ L := by dsimp only [L]; positivity
  have hSmall := (hRadius hD hℓ (hEll.trans <| inv_anti₀ (by positivity)
    (pow_le_pow_right₀ hD₁ (le_max_left A 30)))).1
  have hκ (a : Vec3) (t : ℝ) (ht : t ∈ I) := d.transverseCovector_eq (hsub ht) a
  have hkCenter (t : ℝ) (ht : t ∈ I) :
      labelWaveVector X 0 0 k t = d.oscillation.covector t 0 :=
    (d.transverse_values (hsub ht) 0).2.2.symm
  have hMCenter : EqOn (fun t => fderiv ℝ (U t) (X 0 t 0))
      (fun t => d.oscillation.strain t 0) I := fun t ht => (d.transverse_values (hsub ht) 0).2.1.symm
  have hCenter' : LocalizedAmplitude.CenterWaveOn (fun t => d.oscillation.strain t 0)
      (fun t => d.oscillation.covector t 0) b t₀ T D := by
    have hc := hCenter.congr_gradient hMCenter
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ?_, fun t ht => ?_⟩
    · have hd := hc.covector t ht
      rw [hkCenter t ht] at hd
      exact hd.congr_of_mem (fun u hu => (hkCenter u hu).symm) ht
    · rw [← hkCenter t ht]
      exact hc.nonzero t ht
    · rw [← hkCenter t ht]
      exact hc.amplitude t ht
    · intro z hz hperp u v hu hv huv
      exact hc.stability z (fun t ht => by rw [hkCenter t ht]; exact hz t ht)
        (fun t ht => by rw [hkCenter t ht]; exact hperp t ht) hu hv huv
    · rw [← hkCenter t ht]
      exact hc.coupling t ht
  refine d.mean.transverseForward_of_center d.oscillation ht₀.1 hT₁ hD hκ hCenter'
    (fun a t ht => (d.deformation_value t (hsub ht) a).symm ▸ hF t (hsub ht) a)
    (fun a t ht => (d.transverse_values (hsub ht) a).1.symm ▸ hG t (hsub ht) a)
    (fun a t ht => (d.transverse_values (hsub ht) a).2.1.symm ▸ hM t (hsub ht) _) hL₀ hSmall ?_
  intro a t ht
  have ha := d.transverse_values (hsub ht) a
  have h₀ := d.transverse_values (hsub ht) 0
  rw [d.deformation_value t (hsub ht) a, d.deformation_value t (hsub ht) 0,
    ha.1, h₀.1, ha.2.1, h₀.2.1, ha.2.2, h₀.2.2]
  let Λ := ‖labelWaveVector X 0 0 k t₀‖
  have hΛ : 0 < Λ := norm_pos_iff.mpr (hCenter.nonzero t₀ ⟨le_rfl, ht₀.2⟩).1
  have hLC (p : ℕ) (hp : p ≤ 24) : C * D ^ p * ‖a‖ ≤ L * ‖a‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD₁ hp) hC) (norm_nonneg _)
  have h := hLip hT hT₁ hD₁ hX hU hper hF hG hUjet k hΛ ht₀ rfl t (hsub ht) a 0
  simp only [sub_zero] at h
  exact ⟨h.1.trans (hLC 6 (by decide)), h.2.1.trans (hLC 8 (by decide)),
    h.2.2.1.trans (hLC 7 (by decide)), h.2.2.2.2⟩

section ScaledLabelJets

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_phaseIndependent_word_le (ℓ h : ℝ) (hℓ : 0 ≤ ℓ)
    {f : Vec3 → E} (hf : ContDiff ℝ ∞ f) (w : List (Fin 4)) (x : Vec3 × ℝ) :
    ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun p => f p.1) x‖ ≤
      ℓ ^ w.length * ‖iteratedFDeriv ℝ w.length f x.1‖ := by
  let d (i : Fin 4) : Vec3 × ℝ := hierarchyMixedDirection ℓ h i 0
  have hd (i : Fin 4) : ‖(d i).1‖ ≤ ℓ := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [d, hierarchyMixedDirection, Fin.lastCases_last, phaseCoordinateDirection,
        Prod.smul_fst, smul_zero, norm_zero] using hℓ
    · simp [d, hierarchyMixedDirection, phaseCoordinateDirection, coordinateDirection,
        norm_smul, abs_of_nonneg hℓ]
  let L := ContinuousLinearMap.fst ℝ Vec3 ℝ
  change ‖phaseOperatorWord (fun i _ => d i) w (f ∘ L) x‖ ≤ _
  rw [phaseOperatorWord_constant_eq_iteratedFDeriv d (hf.comp L.contDiff),
    L.iteratedFDeriv_comp_right hf x (by simp)]
  change ‖iteratedFDeriv ℝ w.length f x.1 (fun i => (d (w.get i)).1)‖ ≤ _
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm] using
    (iteratedFDeriv ℝ w.length f x.1).le_opNorm_mul_prod_of_le
      (b := fun _ => ℓ) (fun i => hd (w.get i))

private theorem norm_scaledLabel_jet_eq {f : Vec3 → E} (hf : ContDiff ℝ ∞ f)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (j : ℕ) (a : Vec3) :
    ‖iteratedFDeriv ℝ j (fun x => f (ℓ • x)) a‖ =
      ℓ ^ j * ‖iteratedFDeriv ℝ j f (ℓ • a)‖ := by
  rw [iteratedFDeriv_comp_const_smul ℓ (hf.of_le (by simp)), norm_smul,
    Real.norm_of_nonneg (pow_nonneg hℓ _)]

/-- A label coefficient controlled in the scaled coordinates controls
all of its mixed words at the physical labels. -/
theorem hierarchyRelayWordBound_of_scaledLabelJet {ι : Type*}
    {c : ι → Vec3 → E} {ℓ h B : ℝ} {n : ℕ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    (hc : ∀ t, ContDiff ℝ ∞ (c t))
    (hjet : ∀ t, PhaseJetBound n B (fun a => c t (ℓ • a))) :
    HierarchyRelayWordBound ℓ h n B (fun t p => c t p.1) := by
  refine hierarchyRelayWordBound_of_phaseIndependent hℓ.le hB hc ?_
  intro t j hj a
  have heq : ℓ • (ℓ⁻¹ • a) = a := by
    rw [smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  rw [← heq, ← norm_scaledLabel_jet_eq (hc t) hℓ.le]
  exact hjet t j hj (ℓ⁻¹ • a)

private theorem scaledLabel_jet_of_power {f : Vec3 → E} (hf : ContDiff ℝ ∞ f)
    {ℓ D C : ℝ} {n p q : ℕ} (hℓ : 0 ≤ ℓ) (hD : 1 ≤ D) (hscale : ℓ * D ^ p ≤ 1)
    (hC : 0 ≤ C) (hjet : ∀ j ≤ n, ∀ a,
      ‖iteratedFDeriv ℝ j f a‖ ≤ C * D ^ (p * j + q)) :
    PhaseJetBound n (C * D ^ q) (fun a => f (ℓ • a)) := by
  intro j hj a
  exact (norm_iteratedFDeriv_scaledLabel_power_le hf hD hℓ hscale hC j a
    (hjet j hj _)).1

private theorem norm_phaseIndependent_positive_word_le {ℓ h D C : ℝ} {n : ℕ}
    (hℓ : 0 ≤ ℓ) (hD : 1 ≤ D) (hradius : ℓ ≤ (D ^ 30)⁻¹) (hC : 0 ≤ C)
    {f : Vec3 → E} (hf : ContDiff ℝ ∞ f)
    (hjet : ∀ j ≤ n, ∀ a, ‖iteratedFDeriv ℝ j f a‖ ≤ C * D ^ (16 * j + 11))
    {w : List (Fin 4)} (hw : w ∈ hierarchyAdmissibleWords (Fin 4) n) (hw₀ : w ≠ [])
    (x : Vec3 × ℝ) :
    ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun p => f p.1) x‖ ≤ C * (D ^ 3)⁻¹ := by
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hscale : ℓ * D ^ (16 : ℕ) ≤ 1 := by
    rw [← le_div_iff₀ (pow_pos hD₀ 16), one_div]
    exact hradius.trans (inv_anti₀ (pow_pos hD₀ 16) (pow_le_pow_right₀ hD (by decide)))
  have hwlen : w.length ≤ n := (mem_hierarchyAdmissibleWords.mp hw).1
  have hwpos : 0 < w.length := List.length_pos_iff.mpr hw₀
  let a := ℓ⁻¹ • x.1
  have hcoeff : ℓ ^ w.length * ‖iteratedFDeriv ℝ w.length f x.1‖ ≤ C * ℓ * D ^ (27 : ℕ) := by
    by_cases hzero : ℓ = 0
    · simp [hzero, Nat.ne_of_gt hwpos]
    have heq : ℓ • a = x.1 := by dsimp [a]; rw [smul_smul, mul_inv_cancel₀ hzero, one_smul]
    have h := (norm_iteratedFDeriv_scaledLabel_power_le hf hD hℓ hscale
      hC w.length a (hjet w.length hwlen (ℓ • a))).2 hwpos
    rwa [norm_scaledLabel_jet_eq hf hℓ, heq] at h
  refine (norm_phaseIndependent_word_le ℓ h hℓ hf w x).trans (hcoeff.trans ?_)
  calc
    _ ≤ C * (D ^ 30)⁻¹ * D ^ (27 : ℕ) := by gcongr
    _ = _ := by field_simp [hD₀.ne']

end ScaledLabelJets
/-- The velocity part has degree thirteen in `D`. Its pressure contribution
has degree twenty, while the direct forcing contribution has degree six. -/
theorem transverseSolveNormConstant_scaled_le (n : ℕ) {r D J₀ J R A B : ℝ}
    (hr : r ≤ 1) (hD : 1 ≤ D) (hJ₀ : 0 ≤ J₀) (hJ : 0 ≤ J) (hR : 0 ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    let C := transverseSolveNormConstant n 1 (Real.exp 1) (Real.exp 1 * J₀) J R A B
    0 ≤ C ∧ transverseSolveNormConstant n r (Real.exp 1 * D ^ 3) (Real.exp 1 * J₀)
      (J * D) (R * D ^ 9) (A * D ^ 7) (B * D ^ 6) ≤ C * D ^ 20 := by
  let e : ℝ := Real.exp 1
  let V₀ := transverseVelocityWordConstant n 1 e (e * J₀) J R
  let V := transverseVelocityWordConstant n r (e * D ^ 3) (e * J₀) (J * D) (R * D ^ 9)
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  have he : 0 ≤ e := (Real.exp_pos 1).le
  have hWord := linearODEWordFactor_nonneg (mul_nonneg he hJ₀) n
  have hV₀ : 0 ≤ V₀ := by
    unfold V₀ transverseVelocityWordConstant
    positivity
  have hVeq : V = r * V₀ * D ^ 13 := by
    unfold V V₀ transverseVelocityWordConstant
    ring
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hV13 : V ≤ V₀ * D ^ 13 := by
    rw [hVeq]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hV₀ hr) (pow_nonneg hD₀ 13)
  have hV20 : V ≤ V₀ * D ^ 20 :=
    hV13.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by decide : 13 ≤ 20)) hV₀)
  have hVA : (2 : ℝ) ^ n * (A * D ^ 7) * V ≤ (2 : ℝ) ^ n * A * V₀ * D ^ 20 := by
    calc
      _ ≤ (2 : ℝ) ^ n * (A * D ^ 7) * (V₀ * D ^ 13) :=
        mul_le_mul_of_nonneg_left hV13 (by positivity)
      _ = _ := by ring
  have hFB : (2 : ℝ) ^ n * (B * D ^ 6) ≤ (2 : ℝ) ^ n * B * D ^ 20 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by decide : 6 ≤ 20)) (by positivity)
  change 0 ≤ count * (V₀ + 2 * (count * ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B))) ∧
    count * (V + 2 * (count * ((2 : ℝ) ^ n * (A * D ^ 7) * V + (2 : ℝ) ^ n * (B * D ^ 6)))) ≤
      count * (V₀ + 2 * (count * ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B))) * D ^ 20
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ count * (V₀ * D ^ 20 + 2 * (count *
        ((2 : ℝ) ^ n * A * V₀ * D ^ 20 + (2 : ℝ) ^ n * B * D ^ 20))) := by
      gcongr
    _ = _ := by ring


private theorem phaseJetBound_normalizedPressureSourceCoefficient
    {f : Vec3 → Vec3} {freq BK BQ : ℝ} {N : ℕ}
    (hf : 0 < freq) (hκ : ContDiff ℝ ∞ f) (hκ₀ : ∀ a, f a ≠ 0)
    (hBK : 0 ≤ BK) (hBQ : 0 ≤ BQ)
    (hKjet : PhaseJetBound N BK (fun a => freq⁻¹ • f a))
    (hQjet : PhaseJetBound N BQ (fun a => freq ^ 2 / ‖f a‖ ^ 2)) :
    let c (a : Vec3) := hierarchyRelayPressureSourceCoefficient (freq⁻¹ • f a)
    ContDiff ℝ ∞ c ∧ PhaseJetBound N ((2 : ℝ) ^ N * (BQ * BK)) c := by
  intro c
  let K (a : Vec3) := freq⁻¹ • f a
  let Q (a : Vec3) := freq ^ 2 / ‖f a‖ ^ 2
  let L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  have hKs : ContDiff ℝ ∞ K := hκ.const_smul _
  have hQs : ContDiff ℝ ∞ Q := contDiff_const.div (hκ.norm_sq ℝ)
    (fun a => pow_ne_zero _ (norm_ne_zero_iff.mpr (hκ₀ a)))
  have hL : ContDiff ℝ ∞ (L ∘ K) := L.contDiff.comp hKs
  have heq : c = fun a => Q a • L (K a) := by
    funext a
    have hRecip : (‖K a‖ ^ 2)⁻¹ = Q a := by
      dsimp only [K, Q]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hf.le), mul_pow, mul_inv_rev,
        inv_pow, inv_inv, div_eq_mul_inv, mul_comm]
    change (‖K a‖ ^ 2)⁻¹ • L (K a) = Q a • L (K a)
    rw [hRecip]
  rw [heq]
  exact ⟨hQs.smul hL, phaseJetBound_bilinear_product (lsmul ℝ ℝ) opNorm_lsmul_le hQs hL
    hBQ hBK hQjet (phaseJetBound_comp_left_contraction hKs L (norm_innerSL_le ℝ) hKjet)⟩

set_option maxHeartbeats 1800000 in
/-- Derivative-order constants control the actual coframe, generator and
pressure coefficient words. The measured oscillatory inverse budget
retains a single power `D ^ 20` at every order. -/
theorem exists_parentTransverseCoefficientBudgets_with_unit_duration (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n) :
    ∃ Krec : ℕ → ℝ, (∀ n, 0 ≤ Krec n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ h freq : ℝ} {k : Vec3} {hT : 0 < T},
        T ≤ 1 → t₀ ∈ Icc 0 T → 1 ≤ D → 0 < ℓ → ℓ ≤ (D ^ 30)⁻¹ →
        0 < freq → ‖labelWaveVector X 0 0 k t₀‖ = freq →
        (g : ParentGeometry hT U X k) →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ a,
          ‖iteratedFDeriv ℝ j (U t) a‖ ≤ V n * D ^ j) →
        ∀ n : ℕ, ∃ C Ccomm CJ CR CA CB : ℝ, 0 ≤ C ∧
          (Real.exp 1 * D ^ 3) * (T - t₀) * C ≤ Ccomm ∧
          transverseSolveNormConstant n (T - t₀) (Real.exp 1 * D ^ 3) Ccomm CJ CR CA CB ≤
            Krec n * D ^ 20 ∧
          transverseSolveNormConstant n 1 (Real.exp 1 * D ^ 3) Ccomm CJ CR CA CB ≤
            Krec n * D ^ 20 ∧
          HierarchyRelayWordBound ℓ h n CJ (fun (t : Icc t₀ T) q => g.mean.transverseLift t q.1) ∧
          HierarchyRelayWordBound ℓ h n CR (fun (t : Icc t₀ T) q => g.mean.transversePullback t q.1) ∧
          HierarchyRelayWordBound ℓ h n CA (fun (t : Icc t₀ T) q =>
            hierarchyRelayPressureAmplitudeCoefficient (g.oscillation.strain t q.1)
              (freq⁻¹ • g.oscillation.covector t q.1)) ∧
          HierarchyRelayWordBound ℓ h n CB (fun (t : Icc t₀ T) q =>
            hierarchyRelayPressureSourceCoefficient (freq⁻¹ • g.oscillation.covector t q.1)) ∧
          ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n, w ≠ [] → ∀ t ∈ Icc t₀ T, ∀ q : Vec3 × ℝ,
            ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun p =>
              fixedTransverseGenerator (g.oscillation.strain t p.1) (g.mean.transverseLift t p.1)
                (g.mean.transversePullback t p.1)) q‖ ≤ C := by
  obtain ⟨B, hB, hjets⟩ := exists_parent_coefficientJetBounds V hV
  let J (n : ℕ) := ∑ j ∈ Finset.range (n + 1), B j
  let R (n : ℕ) := (2 : ℝ) ^ n * (J n * (1 + J n))
  let A (n : ℕ) := 2 * ((2 : ℝ) ^ n * (R n * ((2 : ℝ) ^ n * (J n * J n))))
  let PA (n : ℕ) := 2 * ((2 : ℝ) ^ n * (J n * ((2 : ℝ) ^ n * (J n * J n))))
  let PB (n : ℕ) := (2 : ℝ) ^ n * (J n * J n)
  let K (n : ℕ) := transverseSolveNormConstant n 1 (Real.exp 1) (Real.exp 1 * A n)
    (J n) (R n) (PA n) (PB n)
  have hJ (n : ℕ) : 0 ≤ J n := Finset.sum_nonneg fun j _ => hB j
  have hR (n : ℕ) : 0 ≤ R n := by
    have := hJ n
    unfold R
    positivity
  have hA (n : ℕ) : 0 ≤ A n := by
    have := hJ n
    have := hR n
    unfold A
    positivity
  have hPA (n : ℕ) : 0 ≤ PA n := by
    have := hJ n
    unfold PA
    positivity
  have hPB (n : ℕ) : 0 ≤ PB n := by
    have := hJ n
    unfold PB
    positivity
  refine ⟨K, fun n => (transverseSolveNormConstant_scaled_le n (r := 1) le_rfl
    (D := 1) le_rfl (hA n) (hJ n) (hR n) (hPA n) (hPB n)).1, ?_⟩
  intro U X T t₀ D ℓ h freq k hT hT₁ ht₀ hD hℓ hEll hf hFreq d hX hU hper hF hG hUjet n
  have hJn := hJ n
  have hRn := hR n
  have hAn := hA n
  have hPAn := hPA n
  have hPBn := hPB n
  let I := Icc t₀ T
  let F (t : ℝ) (a : Vec3) := fderiv ℝ (X 0 t) a
  let G (t : ℝ) (a : Vec3) := fderiv ℝ (X t 0) (X 0 t a)
  let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
  let κ (t : ℝ) (a : Vec3) := labelWaveVector X 0 a k t
  have hI : I ⊆ Icc 0 T := Icc_subset_Icc_left ht₀.1
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hscale {q : ℕ} (hq : q ≤ 30) : ℓ * D ^ q ≤ 1 := by
    rw [← le_div_iff₀ (pow_pos hD₀ q), one_div]
    exact hEll.trans (inv_anti₀ (pow_pos hD₀ q) (pow_le_pow_right₀ hD hq))
  have hslice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℝ → Vec3 → E}
      (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
      (t : I) : ContDiff ℝ ∞ (u t) :=
    contDiffOn_univ.mp (hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨hI t.property, mem_univ _⟩))
  have hFs (t : I) : ContDiff ℝ ∞ (F t) :=
    hslice (u := F) (hX.contDiffOn_forwardLabelDerivative hT hU hper) t
  have hGs (t : I) : ContDiff ℝ ∞ (G t) :=
    hslice (u := G) (hX.contDiffOn_inverseLabelDerivative hT hU hper) t
  have hMs (t : I) : ContDiff ℝ ∞ (M t) :=
    hslice (u := M) (hX.contDiffOn_materialGradient hT hU hper) t
  have hκs (t : I) : ContDiff ℝ ∞ (κ t) :=
    hslice (u := κ) (hX.contDiffOn_transportedCovector hT hU hper k) t
  have hκ₀ (t : I) (a : Vec3) : κ t a ≠ 0 := by
    rw [show κ t a = d.oscillation.covector t a from (d.transverse_values (hI t.property) a).2.2.symm]
    have hn := d.oscillation.covector_ne_zero t (hI t.property) a
    rwa [d.oscillation.covector_value _ ⟨hI t.property, mem_univ _⟩] at hn
  have hsum (j : ℕ) (hj : j ≤ n) : B j ≤ J n :=
    Finset.single_le_sum (f := B) (fun i _ => hB i) (Finset.mem_range.mpr (by omega))
  have hmono (j : ℕ) (hj : j ≤ n) (p : ℕ) : B j * D ^ p ≤ J n * D ^ p :=
    mul_le_mul_of_nonneg_right (hsum j hj) (pow_nonneg hD₀.le _)
  have hjet (t : I) (j : ℕ) (a : Vec3) :=
    hjets hT hT₁ hD hX hU hper hF hG hUjet k hf ht₀ hFreq j t (hI t.property) a
  let Jfield (t : I) (a : Vec3) := LocalizedAmplitude.coframeLift k (F t a)
  let Rfield (t : I) (a : Vec3) := LocalizedAmplitude.coframePullback k (G t a)
  let Afield (t : I) (a : Vec3) := fixedTransverseGenerator (M t a) (Jfield t a) (Rfield t a)
  have hJRAs (t : I) : ContDiff ℝ ∞ (Jfield t) ∧ ContDiff ℝ ∞ (Rfield t) ∧
      ContDiff ℝ ∞ (Afield t) :=
    LocalizedAmplitude.contDiff_transverseCoframeFields k (hFs t) (hGs t) (hMs t) (hκ₀ t)
  have hJRAjet (t : I) (a : Vec3) := LocalizedAmplitude.norm_iteratedFDeriv_transverseCoframeFields_le
    k ((hFs t).of_le (by simp : (n : ℕ∞ω) ≤ ∞)) ((hGs t).of_le (by simp))
    ((hMs t).of_le (by simp)) (hκ₀ t) a hD (hJ n)
    (fun j hj => (hjet t j a).1.trans (hmono j hj _))
    (fun j hj => (hjet t j a).2.1.trans (hmono j hj _))
    (fun j hj => (hjet t j a).2.2.2.1.trans (hmono j hj _))
    (fun j hj => (hjet t j a).2.2.2.2.2.2.trans (hmono j hj _))
  have hJB : HierarchyRelayWordBound ℓ h n (J n * D) (fun t p => Jfield t p.1) := by
    refine hierarchyRelayWordBound_of_scaledLabelJet hℓ (by positivity)
      (fun t => (hJRAs t).1) fun t => ?_
    simpa only [pow_one] using scaledLabel_jet_of_power (hJRAs t).1 hℓ.le hD (hscale (q := 16) (by decide))
      (hJ n) (q := 1) (fun j hj a => (hJRAjet t a j hj).1)
  have hRB : HierarchyRelayWordBound ℓ h n (R n * D ^ 9) (fun t p => Rfield t p.1) :=
    hierarchyRelayWordBound_of_scaledLabelJet hℓ (by positivity) (fun t => (hJRAs t).2.1) fun t =>
      scaledLabel_jet_of_power (hJRAs t).2.1 hℓ.le hD (hscale (q := 16) (by decide))
        (hR n) (fun j hj a => (hJRAjet t a j hj).2.1)
  have hMscale (t : I) : PhaseJetBound n (J n * D) (fun a => M t (ℓ • a)) := by
    simpa only [pow_one] using scaledLabel_jet_of_power (hMs t) hℓ.le hD
      (hscale (q := 6) (by decide)) (hJ n) (q := 1)
      (fun j hj a => (hjet t j a).2.2.2.1.trans (hmono j hj _))
  have hκscale (t : I) : PhaseJetBound n (J n * D ^ 2) (fun a => freq⁻¹ • κ t (ℓ • a)) :=
    scaledLabel_jet_of_power ((hκs t).const_smul _) hℓ.le hD (hscale (q := 7) (by decide)) (hJ n)
      (fun j hj a => (hjet t j a).2.2.2.2.1.trans (hmono j hj _))
  have hQscale (t : I) : PhaseJetBound n (J n * D ^ 4) (fun a => freq ^ 2 / ‖κ t (ℓ • a)‖ ^ 2) :=
    scaledLabel_jet_of_power (contDiff_const.div ((hκs t).norm_sq ℝ)
      (fun a => pow_ne_zero _ (norm_ne_zero_iff.mpr (hκ₀ t a))))
      hℓ.le hD (hscale (q := 16) (by decide)) (hJ n)
      (fun j hj a => (hjet t j a).2.2.2.2.2.1.trans (hmono j hj _))
  let cA (t : I) (a : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M t a) (freq⁻¹ • κ t a)
  let cB (t : I) (a : Vec3) := hierarchyRelayPressureSourceCoefficient (freq⁻¹ • κ t a)
  have hCBs (t : I) : ContDiff ℝ ∞ (cB t) := by
    let L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
    have hq := (hκs t).const_smul (freq⁻¹)
    have hq₀ (a : Vec3) : freq⁻¹ • κ t a ≠ 0 := smul_ne_zero (inv_ne_zero hf.ne') (hκ₀ t a)
    exact ((hq.norm_sq ℝ).inv (fun a => pow_ne_zero _ (norm_ne_zero_iff.mpr (hq₀ a)))).smul
      (L.contDiff.comp hq)
  have hCAs (t : I) : ContDiff ℝ ∞ (cA t) := by
    have heq : cA t = fun a => (-2 : ℝ) • (cB t a).comp (M t a) := by
      funext a
      simp only [cA, cB, hierarchyRelayPressureAmplitudeCoefficient,
        hierarchyRelayPressureSourceCoefficient, smul_comp, smul_smul]
    rw [heq]
    exact ((hCBs t).clm_comp (hMs t)).const_smul _
  have hCAB : HierarchyRelayWordBound ℓ h n (PA n * D ^ 7) (fun t p => cA t p.1) := by
    refine hierarchyRelayWordBound_of_scaledLabelJet hℓ (by positivity) hCAs fun t => ?_
    have hS : ContDiff ℝ ∞ (fun a : Vec3 => ℓ • a) := contDiff_id.const_smul ℓ
    have h := (phaseJetBound_normalizedPressureAmplitudeCoefficient hf ((hMs t).comp hS)
      ((hκs t).comp hS) (fun a => hκ₀ t (ℓ • a)) (by positivity) (by positivity) (by positivity)
      (hκscale t) (hMscale t) (hQscale t)).2
    convert h using 1 <;> first | rfl | (unfold PA; ring)
  have hCBB : HierarchyRelayWordBound ℓ h n (PB n * D ^ 6) (fun t p => cB t p.1) := by
    refine hierarchyRelayWordBound_of_scaledLabelJet hℓ (by positivity) hCBs fun t => ?_
    have hS : ContDiff ℝ ∞ (fun a : Vec3 => ℓ • a) := contDiff_id.const_smul ℓ
    have h := (phaseJetBound_normalizedPressureSourceCoefficient hf ((hκs t).comp hS)
      (fun a => hκ₀ t (ℓ • a)) (by positivity) (by positivity) (hκscale t) (hQscale t)).2
    convert h using 1 <;> first | rfl | (unfold PB; ring)
  have hJval (t : I) : (fun a => d.mean.transverseLift t a) = Jfield t := by
    funext a
    simp only [MeanCoefficients.transverseLift, Jfield, F, d.deformation_value t (hI t.property) a]
  have hRval (t : I) : (fun a => d.mean.transversePullback t a) = Rfield t := by
    funext a
    simp only [MeanCoefficients.transversePullback, Rfield, G, (d.transverse_values (hI t.property) a).1]
  have hMval (t : I) : d.oscillation.strain t = M t :=
    funext fun a => (d.transverse_values (hI t.property) a).2.1
  have hκval (t : I) : d.oscillation.covector t = κ t :=
    funext fun a => (d.transverse_values (hI t.property) a).2.2
  refine ⟨A n * (D ^ 3)⁻¹, Real.exp 1 * A n, J n * D, R n * D ^ 9, PA n * D ^ 7, PB n * D ^ 6,
    by positivity, ?_, (transverseSolveNormConstant_scaled_le n (by linarith [ht₀.1])
      hD (hA n) (hJ n) (hR n) (hPA n) (hPB n)).2,
      (transverseSolveNormConstant_scaled_le n (r := 1) le_rfl hD
        (hA n) (hJ n) (hR n) (hPA n) (hPB n)).2, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ (Real.exp 1 * D ^ 3) * 1 * (A n * (D ^ 3)⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [ht₀.1])
          (by positivity)) (by positivity)
      _ = _ := by field_simp [hD₀.ne']
  · convert hJB using 1
    funext t p
    exact congrFun (hJval t) p.1
  · convert hRB using 1
    funext t p
    exact congrFun (hRval t) p.1
  · convert hCAB using 1
    funext t p
    rw [hMval t, hκval t]
  · convert hCBB using 1
    funext t p
    rw [hκval t]
  · intro w hw hw₀ t ht p
    let s : I := ⟨t, ht⟩
    have h := norm_phaseIndependent_positive_word_le (h := h) hℓ.le hD hEll (hA n) (hJRAs s).2.2
      (fun j hj a => (hJRAjet s a j hj).2.2) hw hw₀ p
    have hEq : (fun a : Vec3 × ℝ => fixedTransverseGenerator (d.oscillation.strain t a.1)
        (d.mean.transverseLift t a.1) (d.mean.transversePullback t a.1)) = fun a => Afield s a.1 := by
      funext a
      change fixedTransverseGenerator (d.oscillation.strain s a.1) (d.mean.transverseLift s a.1)
        (d.mean.transversePullback s a.1) = Afield s a.1
      rw [hMval s, show d.mean.transverseLift s a.1 = Jfield s a.1 from congrFun (hJval s) _,
        show d.mean.transversePullback s a.1 = Rfield s a.1 from congrFun (hRval s) _]
    rw [hEq]
    exact h

/-- The coefficient estimate for the solve on the actual active duration. -/
theorem exists_parentTransverseCoefficientBudgets (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n) :
    ∃ Krec : ℕ → ℝ, (∀ n, 0 ≤ Krec n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ h freq : ℝ} {k : Vec3} {hT : 0 < T},
        T ≤ 1 → t₀ ∈ Icc 0 T → 1 ≤ D → 0 < ℓ → ℓ ≤ (D ^ 30)⁻¹ →
        0 < freq → ‖labelWaveVector X 0 0 k t₀‖ = freq →
        (g : ParentGeometry hT U X k) →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ a,
          ‖iteratedFDeriv ℝ j (U t) a‖ ≤ V n * D ^ j) →
        ∀ n : ℕ, ∃ C Ccomm CJ CR CA CB : ℝ, 0 ≤ C ∧
          (Real.exp 1 * D ^ 3) * (T - t₀) * C ≤ Ccomm ∧
          transverseSolveNormConstant n (T - t₀) (Real.exp 1 * D ^ 3) Ccomm CJ CR CA CB ≤
            Krec n * D ^ 20 ∧
          HierarchyRelayWordBound ℓ h n CJ (fun (t : Icc t₀ T) q => g.mean.transverseLift t q.1) ∧
          HierarchyRelayWordBound ℓ h n CR (fun (t : Icc t₀ T) q => g.mean.transversePullback t q.1) ∧
          HierarchyRelayWordBound ℓ h n CA (fun (t : Icc t₀ T) q =>
            hierarchyRelayPressureAmplitudeCoefficient (g.oscillation.strain t q.1)
              (freq⁻¹ • g.oscillation.covector t q.1)) ∧
          HierarchyRelayWordBound ℓ h n CB (fun (t : Icc t₀ T) q =>
            hierarchyRelayPressureSourceCoefficient (freq⁻¹ • g.oscillation.covector t q.1)) ∧
          ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n, w ≠ [] → ∀ t ∈ Icc t₀ T, ∀ q : Vec3 × ℝ,
            ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun p =>
              fixedTransverseGenerator (g.oscillation.strain t p.1) (g.mean.transverseLift t p.1)
                (g.mean.transversePullback t p.1)) q‖ ≤ C := by
  obtain ⟨Krec, hK, hBudget⟩ := exists_parentTransverseCoefficientBudgets_with_unit_duration V hV
  refine ⟨Krec, hK, ?_⟩
  intro U X T t₀ D ℓ h freq k hT hT₁ ht₀ hD hℓ hEll hf hFreq d hX hU hper hF hG hjets n
  obtain ⟨C, Ccomm, CJ, CR, CA, CB, hC, hComm, hNum, _, hJ, hBack, hA, hB, hGen⟩ :=
    hBudget (h := h) hT₁ ht₀ hD hℓ hEll hf hFreq d hX hU hper hF hG hjets n
  exact ⟨C, Ccomm, CJ, CR, CA, CB, hC, hComm, hNum, hJ, hBack, hA, hB, hGen⟩


set_option maxHeartbeats 1600000 in
/-- The selected physical hierarchy obeys the measured oscillatory solve
row with the center amplitude as weight and one fixed parent power. -/
theorem exists_physicalTransverseSolveBudget (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n) :
    ∃ (A : ℕ) (Krec : ℕ → ℝ), 30 ≤ A ∧ (∀ n, 0 ≤ Krec n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ h freq : ℝ} {k : Vec3} {b : ℝ → Vec3}
        {hT : 0 < T}, (ht₀ : 0 ≤ t₀) → (htT : t₀ < T) → 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
        (hfreq : 0 < freq) → ‖labelWaveVector X 0 0 k t₀‖ = freq →
        (d : ParentGeometry hT U X k) →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (U t) a‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ a,
          ‖iteratedFDeriv ℝ j (U t) a‖ ≤ V n * D ^ j) →
        LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (U t) (X 0 t 0))
          (fun t => labelWaveVector X 0 0 k t) b t₀ T D →
        ∀ {p : Pressure} {P : ℕ}, (cfg : PhysicalApproximationData d p P) → 1 ≤ P →
          cfg.leading.Inactive t₀ (tsupport (periodizeCentered (radialEnvelope ℓ))) →
          ∀ (hγ : ContinuousOn (fun t => ‖b t‖) (Icc t₀ T))
            (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < ‖b t‖),
          let s := actualMeasuredLevels cfg.operators cfg.profiles P cfg.leading.completionSwitch
            cfg.parentResidual freq hfreq.le ℓ h hT ht₀ htT.le
            (fun t => ‖b t‖) hγ hγ₀
          ∀ n i : ℕ, i ∈ Finset.Icc 2 P → s.osc n i ≤ Krec n * D ^ 20 * s.oscSource n i := by
  obtain ⟨A, hA, hForward⟩ := exists_parentTransverseForward V hV
  obtain ⟨Krec, hKrec, hBudget⟩ := exists_parentTransverseCoefficientBudgets V hV
  refine ⟨A, Krec, hA, hKrec, ?_⟩
  intro U X T t₀ D ℓ h freq k b hT ht₀ htT hD hℓ hEll hf hFreq d hX hU hper hF hG hM hjets hCenter
    p P cfg hP hInactive hγ hγ₀ levels n i hi
  have ht : t₀ ∈ Icc 0 T := ⟨ht₀, htT.le⟩
  have hD₁ : 1 ≤ D := by linarith
  have hEll30 : ℓ ≤ (D ^ 30)⁻¹ :=
    hEll.trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ hD₁ hA))
  obtain ⟨dg, hdg, _, hg, hStable⟩ :=
    hForward cfg.time_le_one ht hD hℓ.le hEll d hX hU hper hF hG hM hjets hCenter
  obtain ⟨C, Ccomm, CJ, CR, CA, CB, hC, hCcomm, hnum, hJ, hR, hA, hB, hgen⟩ :=
    hBudget (h := h) cfg.time_le_one ht hD₁ hℓ hEll30 hf hFreq d hX hU hper hF hG hjets n
  have hK : 0 ≤ Real.exp 1 * D ^ 3 := by positivity
  exact physicalConstruct_oscSolve hT cfg.time_le_one d.inverse d.strain d.covector
    d.mean d.oscillation hP hi ht₀ htT (isClosed_tsupport _) cfg.leading.completionSwitch
    cfg.parentResidual cfg.parentResidual_average cfg.leading.output hInactive.velocity
    hInactive.pressure hInactive.completionSwitch
    (fun a _ ht => d.transverseCovector_eq (Icc_subset_Icc_left ht₀ ht) a) hγ hγ₀ hg hdg
    hf hK hC hCcomm hnum hJ hR hA hB
    (fun q hq => hStable q.1 (by
      obtain ⟨m, hm⟩ := exists_lattice_dist_le_of_mem_periodicEnvelope_tsupport hℓ hq
      exact ⟨m, by rwa [← dist_eq_norm, dist_comm]⟩))
    (fun w hw hw₀ q _ t ht => hgen w hw hw₀ t ht q)

end
end TorusEuler.HierarchyTwistedProfile
