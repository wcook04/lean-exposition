import TorusEuler.HierarchyTwistedCoefficientNorms
import TorusEuler.InductiveParentGeometry
import TorusEuler.ParentVelocityEstimates

/-! The finite derivative seminorm of the actual parent residual. -/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler.InductiveEulerStage.OnSlab

open HierarchyTwistedProfile

/-- The exact residual profile of the parent in (5.10) has the level-two scale.
The constants depend only on the derivative order. -/
theorem exists_residualProfile_unweightedSeminorm_bound :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
        {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}
        (d : s.OnSlab hT k) {ℓ h : ℝ},
        1 ≤ P.frequency 0 → T ≤ 1 → 0 ≤ ℓ → ℓ * (P.frequency n ^ 9) ^ 6 ≤ 1 →
        ∀ m, unweightedSeminorm False ℓ h m hT d.residualProfile ≤
          C m * P.frequency (n + 1) ^ (-5 / 2 : ℝ) := by
  obtain ⟨V, hV, hVelocityJets⟩ := exists_parentVelocityJetBounds
  obtain ⟨J, hJ, hResidualJets⟩ := exists_parentResidualLabelJetBounds V hV
  let C (m : ℕ) := (hierarchyAdmissibleWords (Fin 4) m).card *
    (∑ j ∈ Finset.range (m + 1), J j)
  refine ⟨C, fun m => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => hJ j), ?_⟩
  intro P n activation T s hT k d ℓ h hBase hT₁ hℓ hScale m
  let f := P.frequency n
  let D := f ^ 9
  let next := P.frequency (n + 1)
  let A := next ^ (-5 / 2 : ℝ)
  have hFreqMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hBase P.frequency_step
  have hf : 1 ≤ f := hBase.trans (hFreqMono (Nat.zero_le n))
  have hNext : 1 ≤ next := hBase.trans (hFreqMono (Nat.zero_le (n + 1)))
  have hD : 1 ≤ D := one_le_pow₀ hf
  have hfD : f ≤ D := le_self_pow₀ hf (by decide : (9 : ℕ) ≠ 0)
  have hFiveD : f ^ 5 ≤ D := pow_le_pow_right₀ hf (by decide : (5 : ℕ) ≤ 9)
  have hA : 0 ≤ A := Real.rpow_nonneg (zero_le_one.trans hNext) _
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) : ‖fderiv ℝ (s.flow 0 t) a‖ ≤ D :=
    ((d.deformationOn.bounds t ht).2.1 a).2.trans hfD
  have hG (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) :
      ‖fderiv ℝ (s.flow t 0) (s.flow 0 t a)‖ ≤ D :=
    ((d.deformationOn.bounds t ht).2.2 (s.flow 0 t a)).2.trans hfD
  have hGradient (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      ‖fderiv ℝ (s.velocity t) x‖ ≤ D := by
    let a := s.flow t 0 x
    have hx : s.flow 0 t a = x := (d.deformationOn.bounds t ht).1.2 x
    have hz : (t, a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    have hStrain := d.geometry.mean.norm_strain_le (toUnitTorus a) t ht
    rw [← d.geometry.mean.strain_value _ hz, d.geometry.strain_value _ hz, hx, d.strain_bound]
      at hStrain
    exact hStrain
  have hVelocityBand (t : ℝ) (ht : t ∈ Icc 0 T) :
      RealTorusFourierBand (4 * D) (s.torusVelocity t) := by
    intro j hj
    apply s.velocity_band t (d.subset ht) j
    exact ((show 2 * f ^ 5 ≤ 4 * D by linarith [zero_le_one.trans hD]).trans_lt hj)
  have hResidualBand (t : ℝ) (ht : t ∈ Icc 0 T) :
      RealTorusFourierBand (4 * D) (d.residualTorus t) :=
    fun j hj => d.residualTorus_band t ht j ((mul_le_mul_of_nonneg_left hFiveD (by norm_num)).trans_lt hj)
  have hR (t : ℝ) (ht : t ∈ Icc 0 T) : ‖d.residualTorus t‖ ≤ A := by
    apply (d.residualTorus_bound t ht).trans
    simpa only [A, next, hierarchyMeanExponent, Nat.cast_ofNat, sub_self, zero_div, mul_zero, sub_zero]
      using parentResidual_invCube_le_parentSmall hNext
  have hJets := hResidualJets hT hT₁ hD hA d.deformationOn.flow d.smooth_velocity
    (fun t _ => s.periodic_velocity t) hF hG
    (fun j _ i hi hij t ht => hVelocityJets (s.torusVelocity t) hD (hVelocityBand t ht)
      (hGradient t ht) j i (by omega) hij)
    d.residualTorus hR hResidualBand
  let c (t : Icc (0 : ℝ) T) (a : Vec3) :=
    d.residualTorus t (toUnitTorus (s.flow 0 t a))
  have hc (t : Icc (0 : ℝ) T) : ContDiff ℝ ∞ (c t) := (hJets t t.property).1
  have hvalue (t : Icc (0 : ℝ) T) (x : Vec3 × ℝ) :
      d.residualProfile.val.val.val (t, x) = c t x.1 :=
    (d.residualProfile_value (t, x) ⟨t.property, mem_univ _⟩).trans
      (d.residualTorus_value t t.property (s.flow 0 t x.1)).symm
  have hCoefficient := HierarchyRelayCoefficientJets.of_parent_power_bound
    (h := h) (q := 6) (n := m) hℓ (zero_le_one.trans hD) hA hScale hc
    (fun j _ => hJ j) (fun t j _ a => (hJets t t.property).2 j a)
  exact (unweightedSeminorm_le_of_labelCoefficientJets hT ℓ h m d.residualProfile c
    hvalue hCoefficient).trans_eq (by simp only [C, A, next, mul_assoc])

end TorusEuler.InductiveEulerStage.OnSlab
