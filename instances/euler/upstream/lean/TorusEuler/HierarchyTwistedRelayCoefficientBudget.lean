import TorusEuler.HierarchyTwistedRelayBounds
import TorusEuler.HierarchyRelayCoframeCoefficientBounds
import TorusEuler.HierarchyRelayPotentialCoefficientBounds

/-! Actual parent fields for the finite linear-relay coefficient budgets. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

local notation "Op" => (Vec3 →L[ℝ] Vec3)

/-- The raw parent jet bounds used by the normalized linear relay, on
any time domain contained in the parent slab. -/
structure WaveRelayParentJetData {X : Type*} (D : ℝ) (C : ℕ → ℝ)
    (G M : X → Vec3 → Op) (κnorm : X → Vec3 → Vec3) : Prop where
  coframeSmooth : ∀ t, ContDiff ℝ ∞ (G t)
  strainSmooth : ∀ t, ContDiff ℝ ∞ (M t)
  covectorSmooth : ∀ t, ContDiff ℝ ∞ (κnorm t)
  covectorNeZero : ∀ t a, κnorm t a ≠ 0
  coframe : ∀ t j a, ‖iteratedFDeriv ℝ j (G t) a‖ ≤ C j * D ^ (7 * j + 1)
  strain : ∀ t j a, ‖iteratedFDeriv ℝ j (M t) a‖ ≤ C j * D ^ (6 * j + 1)
  covector : ∀ t j a, ‖iteratedFDeriv ℝ j (κnorm t) a‖ ≤ C j * D ^ (7 * j + 2)
  inverseSquare : ∀ t j a,
    ‖iteratedFDeriv ℝ j (fun b => (‖κnorm t b‖ ^ 2)⁻¹) a‖ ≤ C j * D ^ (16 * j + 4)

set_option maxHeartbeats 1200000 in
/-- Proposition 5.1 supplies the actual transported coframe, strain,
normalized covector and reciprocal squared norm needed by the relay. -/
theorem exists_transportedWaveRelayParentJetData (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j) →
      ∀ {k : Vec3} {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Icc 0 T →
      ‖labelWaveVector X 0 0 k t₀‖ = freq →
      ∀ (G M : HierarchyTwistedProfile T k Op) (κ : HierarchyTwistedProfile T k Vec3),
      (∀ t ∈ Icc 0 T, ∀ a, G.val.val.val (t, a, 0) = fderiv ℝ (X t 0) (X 0 t a)) →
      (∀ t ∈ Icc 0 T, ∀ a, M.val.val.val (t, a, 0) = fderiv ℝ (U t) (X 0 t a)) →
      (∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) = labelWaveVector X 0 a k t) →
      ∀ {S : Set ℝ}, S ⊆ Icc 0 T →
      WaveRelayParentJetData D C
        (fun (t : S) a => G.val.val.val (t, a, 0))
        (fun (t : S) a => M.val.val.val (t, a, 0))
        (fun (t : S) a => freq⁻¹ • κ.val.val.val (t, a, 0)) := by
  obtain ⟨C, hC, hCoef⟩ := exists_parent_coefficientJetBounds R hR
  refine ⟨C, hC, ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hG hUjet k freq t₀ hfreq ht₀ hcenter
    G M κ hGval hMval hκval S hS
  have hsmooth (f : HierarchyTwistedProfile T k Op) (t : S) :
      ContDiff ℝ ∞ (fun a => f.val.val.val (t, a, 0)) :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val (hS t.property)).comp
      (contDiff_id.prodMk contDiff_const)
  have hUpper := hCoef hT hT₁ hD hX hU hper hF hG hUjet k hfreq ht₀ hcenter
  have hSmoothκ (t : S) : ContDiff ℝ ∞
      (fun a => freq⁻¹ • κ.val.val.val (t, a, 0)) := by
    have hbase : ContDiff ℝ ∞ (fun a => κ.val.val.val (t, a, 0)) :=
      (HierarchySmoothProfile.contDiff_labelPhase_slice κ.val.val (hS t.property)).comp
        (contDiff_id.prodMk contDiff_const)
    exact (contDiff_const (c := freq⁻¹)).smul hbase
  refine ⟨hsmooth G, hsmooth M, hSmoothκ, ?_, ?_, ?_, ?_, ?_⟩
  · intro t a
    have ht := hS t.property
    have hD₀ : 0 < D := zero_lt_one.trans_le hD
    have hb := hX.norm_normalizedLabelWaveVector_bounds hT (hU.of_le (by simp)) hper
      ht₀ ht a k hD hfreq hcenter (hF _ ht₀ _) (hG _ ht₀ _) (hF _ ht _) (hG _ ht _)
    rw [hκval t ht a]
    exact norm_ne_zero_iff.mp (ne_of_gt ((by positivity : 0 < (D ^ 2)⁻¹).trans_le hb.2.1))
  · intro t j a
    simpa only [hGval t (hS t.property)] using (hUpper j t (hS t.property) a).2.1
  · intro t j a
    simpa only [hMval t (hS t.property)] using (hUpper j t (hS t.property) a).2.2.2.1
  · intro t j a
    simpa only [hκval t (hS t.property)] using (hUpper j t (hS t.property) a).2.2.2.2.1
  · intro t j a
    simpa only [hκval t (hS t.property), inv_sq_norm_inv_smul] using
      (hUpper j t (hS t.property) a).2.2.2.2.2.1

/-- In the actual parent chart the coframe and covector solve the two
closed-slab geometric differential equations of the relay. -/
theorem transportedWaveRelay_coefficient_timeEquations
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ} {k : Vec3} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (G M : HierarchyTwistedProfile T k Op) (κ : HierarchyTwistedProfile T k Vec3)
    (hGval : ∀ t ∈ Icc 0 T, ∀ a, G.val.val.val (t, a, 0) = fderiv ℝ (X t 0) (X 0 t a))
    (hMval : ∀ t ∈ Icc 0 T, ∀ a, M.val.val.val (t, a, 0) = fderiv ℝ (U t) (X 0 t a))
    (hκval : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) = labelWaveVector X 0 a k t) :
    (∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => G.val.val.val (r, a, 0))
      (-((G.val.val.val (t, a, 0)).comp (M.val.val.val (t, a, 0)))) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  constructor
  · intro t ht a
    have h := hX.hasDerivWithinAt_inverseLabelCoframe hT hU hper h0 ht a
    rw [← hGval t ht a, ← hMval t ht a] at h
    exact h.congr_of_mem (fun r hr => hGval r hr a) ht
  · intro t ht a
    have h := hX.hasDerivWithinAt_labelWaveVector hT hU hper h0 ht a k
    rw [← hκval t ht a, ← hMval t ht a] at h
    exact h.congr_of_mem (fun r hr => hκval r hr a) ht

private theorem relayCoefficientJets_mono {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ℓ h : ℝ} {n : ℕ} {A B : ℝ} {c : X → Vec3 → E}
    (hc : HierarchyRelayCoefficientJets ℓ h n A c) (hAB : A ≤ B) :
    HierarchyRelayCoefficientJets ℓ h n B c :=
  ⟨hc.1, hc.2.1.trans hAB, fun w hw t x => (hc.2.2 w hw t x).trans hAB⟩

/-- Assemble the potential and pressure estimates and the three geometric
row estimates under a common coefficient bound. -/
theorem WaveRelayCoefficientBudget.of_parts
    {X : Type*} {ℓ h : ℝ} {n : ℕ} {Kp Kg K : ℝ}
    {G M : X → Vec3 → Op} {κnorm : X → Vec3 → Vec3}
    (hKp : Kp ≤ K) (hKg : Kg ≤ K)
    (hp : HierarchyRelayCoefficientJets ℓ h (n + 1) Kp
        (fun t a => hierarchyRelayPotentialCoefficient (κnorm t a)) ∧
      HierarchyRelayCoefficientJets ℓ h (n + 1) Kp
        (fun t a => hierarchyRelayTimeAmplitudeCoefficient (M t a) (κnorm t a)) ∧
      HierarchyRelayCoefficientJets ℓ h (n + 1) Kp
        (fun t a => hierarchyRelayPressureAmplitudeCoefficient (M t a) (κnorm t a)) ∧
      HierarchyRelayCoefficientJets ℓ h (n + 1) Kp
        (fun t a => hierarchyRelayPressureSourceCoefficient (κnorm t a)))
    (hg : (∀ i, HierarchyRelayCoefficientJets ℓ h n Kg
        (fun t a => hierarchyRelayCurlRow ℓ (G t a) i)) ∧
      (∀ i, HierarchyRelayCoefficientJets ℓ h n Kg
        (fun t a => hierarchyRelayMaterialRow ℓ (G t a) (M t a) i)) ∧
      (∀ i, HierarchyRelayCoefficientJets ℓ h n Kg
        (fun t a => hierarchyRelayPressureRow ℓ (G t a) i))) :
    WaveRelayCoefficientBudget ℓ h n K G M κnorm :=
  ⟨relayCoefficientJets_mono hp.1 hKp, relayCoefficientJets_mono hp.2.1 hKp,
    relayCoefficientJets_mono hp.2.2.1 hKp, relayCoefficientJets_mono hp.2.2.2 hKp,
    fun i => relayCoefficientJets_mono (hg.1 i) hKg,
    fun i => relayCoefficientJets_mono (hg.2.1 i) hKg,
    fun i => relayCoefficientJets_mono (hg.2.2 i) hKg⟩

/-- Increasing the common budget preserves every normalized relay row estimate. -/
theorem WaveRelayCoefficientBudget.mono {X : Type*} {ℓ h : ℝ} {n : ℕ} {A B : ℝ}
    {G M : X → Vec3 → Op} {κnorm : X → Vec3 → Vec3}
    (hA : WaveRelayCoefficientBudget ℓ h n A G M κnorm) (hAB : A ≤ B) :
    WaveRelayCoefficientBudget ℓ h n B G M κnorm :=
  .of_parts hAB hAB ⟨hA.potential, hA.potentialTime, hA.pressureAmplitude, hA.pressureSource⟩
    ⟨hA.curl, hA.material, hA.gradient⟩

/-- The inverse label width may be absorbed into a fixed parent power after
the width has been chosen. -/
theorem WaveRelayCoefficientBudget.absorb_inverse_width {X : Type*}
    {ℓ h D L : ℝ} {n q : ℕ} {G M : X → Vec3 → Op} {κnorm : X → Vec3 → Vec3}
    (hD : 1 ≤ D) (hL : 0 ≤ L) (hℓInv : ‖ℓ⁻¹‖ ≤ D ^ q)
    (hBudget : WaveRelayCoefficientBudget ℓ h n (L * (1 + ‖ℓ⁻¹‖) * D ^ (15 : ℕ)) G M κnorm) :
    WaveRelayCoefficientBudget ℓ h n (2 * L * D ^ (15 + q)) G M κnorm := by
  apply hBudget.mono
  have hDq : 1 ≤ D ^ q := one_le_pow₀ hD
  calc
    _ ≤ L * (2 * D ^ q) * D ^ (15 : ℕ) := by
      gcongr
      linarith
    _ = _ := by rw [pow_add]; ring

/-- The four normalized potential and pressure coefficients and the three
geometric rows have one common bound with a fixed parent exponent. -/
theorem exists_waveRelayCoefficientBudget_of_parentJetData
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) :
    ∃ L : ℕ → ℝ, (∀ n, 0 ≤ L n) ∧
      ∀ {X : Type*} {ℓ h D : ℝ}, 0 ≤ ℓ → 1 ≤ D → ℓ * D ^ (16 : ℕ) ≤ 1 →
      ∀ (n : ℕ) {G M : X → Vec3 → Op} {κnorm : X → Vec3 → Vec3},
      WaveRelayParentJetData D C G M κnorm →
      WaveRelayCoefficientBudget ℓ h n (L n * (1 + ‖ℓ⁻¹‖) * D ^ (15 : ℕ)) G M κnorm := by
  obtain ⟨K, hK, hPotential⟩ := exists_hierarchyRelayPotentialCoefficientBounds C hC
  let J (n : ℕ) := hierarchyRelayGeometricRowBudget C n 1 1
  have hJ (n : ℕ) : 0 ≤ J n := by
    have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), C i := Finset.sum_nonneg fun i _ => hC i
    dsimp only [J, hierarchyRelayGeometricRowBudget]
    positivity
  let L (n : ℕ) := K (n + 1) + J n
  have hL (n : ℕ) : 0 ≤ L n := add_nonneg (hK _) (hJ _)
  refine ⟨L, hL, ?_⟩
  intro X ℓ h D hℓ hD hscale n G M κnorm d
  have hp := hPotential (h := h) hℓ hD hscale (n + 1) M κnorm
    d.strainSmooth d.covectorSmooth d.covectorNeZero
    (fun t j _ a => d.strain t j a) (fun t j _ a => d.covector t j a)
    (fun t j _ a => d.inverseSquare t j a)
  have hg := hierarchyRelayGeometricCoefficientJets_of_parent_power_bounds (h := h)
    n C G M hℓ hD hscale (fun j _ => hC j) d.coframeSmooth d.strainSmooth
    (fun t j _ a => d.coframe t j a) (fun t j _ a => d.strain t j a)
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hInv : 1 ≤ 1 + ‖ℓ⁻¹‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hpbound : K (n + 1) * D ^ (15 : ℕ) ≤ L n * (1 + ‖ℓ⁻¹‖) * D ^ (15 : ℕ) :=
    mul_le_mul_of_nonneg_right
      ((le_add_of_nonneg_right (hJ n)).trans (le_mul_of_one_le_right (hL n) hInv))
      (pow_nonneg hD₀ _)
  have hgBound : hierarchyRelayGeometricRowBudget C n ℓ D ≤
      L n * (1 + ‖ℓ⁻¹‖) * D ^ (15 : ℕ) := by
    calc
      _ = (J n * ‖ℓ⁻¹‖) * D ^ (2 : ℕ) := by
        simp [J, hierarchyRelayGeometricRowBudget, mul_assoc]
      _ ≤ L n * (1 + ‖ℓ⁻¹‖) * D ^ (15 : ℕ) :=
        mul_le_mul
          (mul_le_mul (le_add_of_nonneg_left (hK (n + 1)))
            (le_add_of_nonneg_left zero_le_one) (norm_nonneg _) (hL n))
          (pow_le_pow_right₀ hD (by norm_num)) (pow_nonneg hD₀ _)
          (mul_nonneg (hL n) (add_nonneg zero_le_one (norm_nonneg _)))
  exact WaveRelayCoefficientBudget.of_parts hpbound hgBound hp hg

set_option maxHeartbeats 950000 in
/-- The transported parent coefficients furnish the actual normalized
linear-relay budget at every finite word order. -/
theorem exists_transportedWaveRelayCoefficientBudget (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ L : ℕ → ℝ, (∀ n, 0 ≤ L n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j) →
      ∀ {k : Vec3} {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Icc 0 T →
      ‖labelWaveVector X 0 0 k t₀‖ = freq →
      ∀ (G M : HierarchyTwistedProfile T k Op) (κ : HierarchyTwistedProfile T k Vec3),
      (∀ t ∈ Icc 0 T, ∀ a, G.val.val.val (t, a, 0) = fderiv ℝ (X t 0) (X 0 t a)) →
      (∀ t ∈ Icc 0 T, ∀ a, M.val.val.val (t, a, 0) = fderiv ℝ (U t) (X 0 t a)) →
      (∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) = labelWaveVector X 0 a k t) →
      ∀ {S : Set ℝ}, S ⊆ Icc 0 T →
      ∀ {ℓ h : ℝ}, 0 ≤ ℓ → ℓ * D ^ (16 : ℕ) ≤ 1 → ∀ n,
      WaveRelayCoefficientBudget ℓ h n (L n * (1 + ‖ℓ⁻¹‖) * D ^ (15 : ℕ))
        (fun (t : S) a => G.val.val.val (t, a, 0))
        (fun (t : S) a => M.val.val.val (t, a, 0))
        (fun (t : S) a => freq⁻¹ • κ.val.val.val (t, a, 0)) := by
  obtain ⟨C, hC, hData⟩ := exists_transportedWaveRelayParentJetData R hR
  obtain ⟨L, hL, hBudget⟩ := exists_waveRelayCoefficientBudget_of_parentJetData C hC
  refine ⟨L, hL, ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hG hUjet k freq t₀ hfreq ht₀ hcenter
    G M κ hGval hMval hκval S hS ℓ h hℓ hscale n
  exact hBudget hℓ hD hscale n
    (hData hT hT₁ hD hX hU hper hF hG hUjet hfreq ht₀ hcenter G M κ hGval hMval hκval hS)

end

end TorusEuler.HierarchyTwistedProfile
