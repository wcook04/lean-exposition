import TorusEuler.HierarchySelectedLinearEstimates

/-! The physical curl and linear relay estimates of Lemma 5.5. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile.ParentGeometry

open PhysicalApproximationData

variable {U : Velocity} {X : ℝ → Velocity} {T : ℝ} {k : Vec3} {hT : 0 < T}

local notation "I" => Icc 0 T
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- Lemma 5.5 (cc:uf:hier:lem:relay) with the true weight and transported
coefficients. The parent exponent is fixed once the envelope exponent
is chosen, independently of the order or the field. The homogeneous
case is obtained by taking the force to be zero. -/
theorem paper_hierarchy_relay (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D t₀ freq h : ℝ} {k : Vec3} {hT : 0 < T}
        (d : ParentGeometry hT U X k) (a : ℕ),
        16 ≤ a → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X t 0) (X 0 t x)‖ ≤ D) →
        (∀ n j, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j) →
        (hf : 0 < freq) → (ht₀ : 0 ≤ t₀) → (htT : t₀ < T) →
        ‖labelWaveVector X 0 0 k t₀‖ = freq →
        ∀ (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t) (n : ℕ),
        let ℓ := (D ^ a)⁻¹
        let W := fun j => amplitudeSeminorm (E := Vec3) (k := k) False ℓ h j hT ht₀ htT.le γ hγ hpos
        let K := C n * D ^ (2 * (15 + a)) * freq⁻¹
        let A := twistedHierarchyOperators hT d.inverse d.strain d.covector
        let curl := complete hT d.inverse d.covector d.oscillation.covector_independent
          d.oscillation.covector_ne_zero
        ∀ (V : HierarchyTwistedProfile T k Vec3), A.average V = 0 →
        (∀ t ∈ Icc t₀ T, ∀ x s,
          ⟪d.covector.val.val.val (t, x, 0), V.val.val.val (t, x, s)⟫_ℝ = 0) →
        W n (curl V) ≤ K * W (n + 1) V ∧
          ∀ (F : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ),
            A.average F = 0 →
            (∀ t ∈ Icc t₀ T, ∀ x, phaseMean (fun s => q.val.val.val (t, x, s)) = 0) →
            (∀ t ∈ Icc t₀ T, ∀ x s,
              (A.material V + A.phaseGrad q).val.val.val (t,x,s) = F.val.val.val (t,x,s)) →
            W n (A.material (curl V) + A.labelGrad q) ≤ K * (W (n + 1) V + W (n + 1) F) := by
  obtain ⟨L, hL, hCoeffs⟩ := exists_transportedWaveRelayCoefficientBudget R hR
  let C (n : ℕ) := max (completionOrderConstant n) (waveRelayOrderConstant n) * (2 * L n) ^ 2
  have hCompletion (n : ℕ) : 0 ≤ completionOrderConstant n := by
    unfold completionOrderConstant
    positivity
  have hRelay (n : ℕ) : 0 ≤ waveRelayOrderConstant n := by
    unfold waveRelayOrderConstant
    positivity
  refine ⟨C, fun n => mul_nonneg ((hCompletion n).trans (le_max_left _ _)) (sq_nonneg _), ?_⟩
  intro U X T D t₀ freq h k hT d a ha hT₁ hD hX hU hper hF hG hjets hf ht₀ htT hFreq γ hγ hpos n
    ℓ W K A curl V hV htrans
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hD₀ _)
  have h₁ : ℓ * D ^ (16 : ℕ) ≤ 1 :=
    ((mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD ha) hℓ.le)).trans
      (inv_mul_cancel₀ (pow_ne_zero _ hD₀.ne')).le
  have hI : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hCoeff₀ := hCoeffs hT hT₁ hD hX hU hper hF hG hjets hf ⟨ht₀,htT.le⟩ hFreq
    d.inverse d.strain d.covector
    (fun t ht x => d.inverse_value (t,x,0) ⟨ht,mem_univ _⟩)
    (fun t ht x => d.strain_value (t,x,0) ⟨ht,mem_univ _⟩)
    (fun t ht x => d.covector_value (t,x,0) ⟨ht,mem_univ _⟩) hI (h := h) hℓ.le h₁ n
  let B := 2 * L n * D ^ (15 + a)
  have hwidth : 1 + ‖ℓ⁻¹‖ ≤ 2 * D ^ a := by
    have hEq : ℓ⁻¹ = D ^ a := inv_inv _
    rw [hEq, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hD₀.le _)]
    linarith [one_le_pow₀ hD (n := a)]
  have hCoeff := hCoeff₀.mono (show L n * (1 + ‖ℓ⁻¹‖) * D ^ (15 : ℕ) ≤ B by
    calc
      _ ≤ L n * (2 * D ^ a) * D ^ (15 : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (hL n)) (by positivity)
      _ = _ := by unfold B; rw [pow_add]; ring)
  obtain ⟨Bγ,hBγ⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT.le) hγ hpos
  have hCap (Z : ℝ) (hZ : Z ≤ max (completionOrderConstant n) (waveRelayOrderConstant n)) :
      Z * B ^ 2 * freq⁻¹ ≤ K := by
    calc
      _ ≤ max (completionOrderConstant n) (waveRelayOrderConstant n) * B ^ 2 * freq⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZ (sq_nonneg _))
          (inv_nonneg.mpr hf.le)
      _ = _ := by dsimp only [B, K, C]; rw [mul_pow, ← pow_mul, Nat.mul_comm (15 + a) 2]; ring
  constructor
  · have h := boundedWeightSeminorm_complete_le hT d.inverse d.covector V d.mean.inverse_independent
      d.oscillation.covector_independent d.oscillation.covector_ne_zero hV hI (fun t => (γ t)⁻¹)
      hBγ ℓ h hℓ.ne' n hf hCoeff.curl hCoeff.potential
    change W n (curl V) ≤ completionOrderConstant n * B ^ 2 * freq⁻¹ * W (n + 1) V at h
    exact h.trans (mul_le_mul_of_nonneg_right (hCap _ (le_max_left _ _)) (apply_nonneg _ _))
  · intro F q hFav hq hMom
    have hGeom := transportedWaveRelay_coefficient_timeEquations hT hX (hU.of_le (by simp)) hper
      d.inverse d.strain d.covector
      (fun t ht x => d.inverse_value (t,x,0) ⟨ht,mem_univ _⟩)
      (fun t ht x => d.strain_value (t,x,0) ⟨ht,mem_univ _⟩)
      (fun t ht x => d.covector_value (t,x,0) ⟨ht,mem_univ _⟩)
    have hEval (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3 × ℝ) :
        (A.material (curl V) + A.labelGrad q).val.val.val (t,x) =
          waveRelayAt d.inverse d.strain d.covector V F t x :=
      material_complete_add_labelGrad_apply_relay_of_momentum_on hT d.inverse d.strain d.covector V F q
        ht₀ htT d.mean.inverse_independent (parentStrain_phaseIndependent (d := d))
        d.oscillation.covector_independent d.oscillation.covector_ne_zero hV hGeom.1 hGeom.2
        htrans hq hMom ht x
    have h := boundedWeightSeminorm_waveRelay_le_of_eval hT d.inverse d.strain d.covector V F
      (A.material (curl V) + A.labelGrad q) ℓ h hℓ.ne' n hf hI (fun t => (γ t)⁻¹) hBγ
      hV hFav hEval hCoeff
    change W n (A.material (curl V) + A.labelGrad q) ≤
      waveRelayOrderConstant n * B ^ 2 * freq⁻¹ * (W (n + 1) V + W (n + 1) F) at h
    exact h.trans (mul_le_mul_of_nonneg_right (hCap _ (le_max_right _ _))
      (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))

end TorusEuler.HierarchyTwistedProfile.ParentGeometry
