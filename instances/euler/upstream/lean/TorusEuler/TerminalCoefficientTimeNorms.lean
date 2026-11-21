import TorusEuler.TerminalCoefficientTimeBase
import TorusEuler.TerminalTimeJetNorms
import TorusEuler.HierarchyTwistedCoefficientNorms
import TorusEuler.InductiveParentGeometry

/-! Scaled profile seminorms for the mixed jets of the actual label coefficients. -/

open ContinuousLinearMap Finset Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

/-- The finite composition and summation constant for the label time norm.
The derivative slope is absorbed by the label length before these sums. -/
def terminalLabelTimeSeminormCost (C : ℕ → ℝ) (q n : ℕ) : ℝ :=
  (q + 1 : ℝ) * ((hierarchyAdmissibleWords (Fin 4) n).card *
    ∑ j ∈ range (n + 1), C j)

theorem terminalLabelTimeSeminormCost_nonneg {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (q n : ℕ) : 0 ≤ terminalLabelTimeSeminormCost C q n :=
  mul_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun j _ => hC j))

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Read the derivative at fixed label and phase from the exact closed-slab
time jet of the physical label field. -/
theorem timeJet_eval_of_labelField {f : ℝ → Vec3 → E} (hT : 0 < T)
    (profile : HierarchyTwistedProfile T k E)
    (hVal : ∀ x ∈ hierarchyProfileSlab T, profile.val.val.val x = f x.1 x.2.1)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (timeJet hT i profile).val.val.val (t, x) = slabTimeJet 0 T i f t x.1 := by
  rw [timeJet_apply hT i profile ht]
  exact iteratedDerivWithin_congr (fun u hu => hVal (u, x) ⟨hu, mem_univ _⟩) ht

private theorem contDiffOn_labelField_of_eval {f : ℝ → Vec3 → E}
    (profile : HierarchyTwistedProfile T k E)
    (hVal : ∀ x ∈ hierarchyProfileSlab T, profile.val.val.val x = f x.1 x.2.1) :
    ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  refine ((HierarchySmoothProfile.smooth profile.val.val).comp
    (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const))
    (fun z hz => ⟨hz.1, mem_univ (z.2, (0 : ℝ))⟩)).congr ?_
  intro x hx
  exact (hVal (x.1, x.2, 0) ⟨hx.1, mem_univ _⟩).symm

/-- Each measured spatial derivative of a time jet has the same amplitude
as the label field's zeroth spatial order. -/
theorem unweightedSeminorm_timeJet_le_of_labelMixedJetBound {f : ℝ → Vec3 → E}
    {ℓ h D A : ℝ} {q p : ℕ} {C : ℕ → ℝ} (hT : 0 < T)
    (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hScale : ℓ * D ^ p ≤ 1)
    (profile : HierarchyTwistedProfile T k E)
    (hVal : ∀ x ∈ hierarchyProfileSlab T, profile.val.val.val x = f x.1 x.2.1)
    (hRaw : TerminalMixedJetBound 0 T q p D A C f)
    (hC : ∀ n, 0 ≤ C n) (n : ℕ) {i : ℕ} (hi : i ≤ q) :
    unweightedSeminorm False ℓ h n hT (timeJet hT i profile) ≤
      ((hierarchyAdmissibleWords (Fin 4) n).card * ∑ j ∈ range (n + 1), C j) * A := by
  let c (t : Icc (0 : ℝ) T) := slabTimeJet 0 T i f t
  have hSmooth := contDiffOn_labelField_of_eval profile hVal
  have hJet : HierarchyRelayCoefficientJets ℓ h n ((∑ j ∈ range (n + 1), C j) * A) c :=
    HierarchyRelayCoefficientJets.of_parent_power_bound (q := p) hℓ hD hA hScale
      (fun t => slabTimeJet_slice_smooth hT hSmooth i t.property)
      (fun j _ => hC j) (fun t j _ x => hRaw i hi j t t.property x)
  simpa only [mul_assoc] using
    unweightedSeminorm_le_of_labelCoefficientJets hT ℓ h n (timeJet hT i profile) c
      (fun t x => timeJet_eval_of_labelField hT profile hVal i t.property x) hJet

/-- The factorial time norm of a transported coefficient or residual
keeps the raw amplitude and has a fixed order-dependent constant. -/
theorem unweighted_timeJetSeminorm_le_of_labelMixedJetBound {f : ℝ → Vec3 → E}
    {ℓ h D A : ℝ} {q p : ℕ} {C : ℕ → ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hScale : ℓ * D ^ p ≤ 1)
    (profile : HierarchyTwistedProfile T k E)
    (hVal : ∀ x ∈ hierarchyProfileSlab T, profile.val.val.val x = f x.1 x.2.1)
    (hRaw : TerminalMixedJetBound 0 T q p D A C f) (hC : ∀ n, 0 ≤ C n) (n : ℕ) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) profile ≤
      terminalLabelTimeSeminormCost C q n * A := by
  let B : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card * ∑ j ∈ range (n + 1), C j
  have hB : 0 ≤ B * A :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun j _ => hC j)) hA
  have hWeight (i : ℕ) : terminalTimeJetWeight T i ≤ 1 := by
    have hi : (1 : ℝ) ≤ i.factorial := by
      exact_mod_cast (Nat.factorial_pos i : 0 < i.factorial)
    exact (div_le_one (by positivity)).mpr ((pow_le_one₀ hT.le hT₁).trans hi)
  rw [timeJetSeminorm_apply]
  calc
    _ ≤ ∑ _ ∈ range (q + 1), B * A := by
      refine sum_le_sum fun i hi => ?_
      exact (mul_le_mul_of_nonneg_left
        (unweightedSeminorm_timeJet_le_of_labelMixedJetBound hT hℓ hD hA hScale
          profile hVal hRaw hC n (Nat.lt_succ_iff.mp (mem_range.mp hi)))
        (terminalTimeJetWeight_pos hT i).le).trans (mul_le_of_le_one_left hB (hWeight i))
    _ = _ := by simp [terminalLabelTimeSeminormCost, B, mul_assoc, nsmul_eq_mul]

/-- Apply the mixed time bound to a smooth periodic label coefficient
embedded in the actual twisted hierarchy. -/
theorem ofLabelField_unweighted_timeJetSeminorm_le {f : ℝ → Vec3 → E}
    {ℓ h D A : ℝ} {q p : ℕ} {C : ℕ → ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hScale : ℓ * D ^ p ≤ 1) (k : Vec3)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (f t))
    (hRaw : TerminalMixedJetBound 0 T q p D A C f) (hC : ∀ n, 0 ≤ C n) (n : ℕ) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) (ofLabelField k f hf hper) ≤
      terminalLabelTimeSeminormCost C q n * A :=
  unweighted_timeJetSeminorm_le_of_labelMixedJetBound hT hT₁ hℓ hD hA hScale
    (ofLabelField k f hf hper) (fun _ hx => ofLabelField_eval k f hf hper hx) hRaw hC n

/-- The normalized transported covector gives the fast coefficient's mixed
time norm, with the carrier and phase losses made explicit together. -/
theorem scaledPhaseCoefficientProfile_unweighted_timeJetSeminorm_le
    {f : ℝ → Vec3 → Vec3} {ℓ h D A freq : ℝ} {q p : ℕ} {C : ℕ → ℝ}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hScale : ℓ * D ^ p ≤ 1) (hFreq : 0 < freq) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (κ : HierarchyTwistedProfile T k Vec3)
    (hVal : ∀ x ∈ hierarchyProfileSlab T, κ.val.val.val x = f x.1 x.2.1)
    (hRaw : TerminalMixedJetBound 0 T q p D A C (fun t x => freq⁻¹ • f t x))
    (hC : ∀ n, 0 ≤ C n) (n : ℕ) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) (scaledPhaseCoefficientProfile h κ) ≤
      terminalLabelTimeSeminormCost C q n * A * freq ^ (3 / 2 : ℝ) := by
  let factor := freq ^ (3 / 2 : ℝ)
  let L : Vec3 →L[ℝ] (Vec3 →L[ℝ] ℝ) := (h⁻¹ * freq) • innerSL ℝ
  let c (t : ℝ) (a : Vec3) := L (freq⁻¹ • f t a)
  have hfactor : 0 ≤ factor := Real.rpow_nonneg hFreq.le _
  have hEq : h⁻¹ * freq = factor := by
    rw [hWidth, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hFreq.le, inv_inv]
    change freq ^ (1 / 2 : ℝ) * freq = freq ^ (3 / 2 : ℝ)
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hFreq, Real.rpow_one]
  have hL : ‖L‖ ≤ factor := by
    apply L.opNorm_le_bound hfactor
    intro v
    change ‖(h⁻¹ * freq) • innerSL ℝ v‖ ≤ factor * ‖v‖
    rw [norm_smul, hEq, Real.norm_of_nonneg hfactor, innerSL_apply_norm]
  have hSmooth : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => freq⁻¹ • f t x))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (contDiffOn_labelField_of_eval κ hVal).const_smul _
  have hBound := hRaw.apply_clm hT hSmooth L
  have hMapped : TerminalMixedJetBound 0 T q p D (A * factor) C c := by
    intro i hi j t ht x
    refine (hBound i hi j t ht x).trans ?_
    calc
      _ ≤ (factor * C j) * A * D ^ (p * j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL (hC j)) hA) (pow_nonneg hD _)
      _ = _ := by ring
  have hc (x : HierarchyProfilePoint) (hx : x ∈ hierarchyProfileSlab T) :
      (scaledPhaseCoefficientProfile h κ).val.val.val x = c x.1 x.2.1 := by
    rcases x with ⟨t, a, s⟩
    rw [scaledPhaseCoefficientProfile_apply h κ hx.1, hVal _ hx]
    change h⁻¹ • innerSL ℝ (f t a) = (h⁻¹ * freq) • innerSL ℝ (freq⁻¹ • f t a)
    rw [map_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hFreq.ne', mul_one]
  simpa only [mul_assoc] using unweighted_timeJetSeminorm_le_of_labelMixedJetBound
    hT hT₁ hℓ hD (mul_nonneg hA hfactor) hScale (scaledPhaseCoefficientProfile h κ) hc hMapped hC n

end HierarchyTwistedProfile

namespace InductiveEulerStage.OnSlab

open HierarchyTwistedProfile

/-- The exact parent residual in the selected mean source inherits its
transported mixed time bound at the fixed label length. -/
theorem residualProfile_unweighted_timeJetSeminorm_le
    {P : InductiveEulerParameters} {j : ℕ} {activation T ℓ h D A : ℝ} {q p : ℕ} {C : ℕ → ℝ}
    {s : InductiveEulerStage P j activation} {hT : 0 < T} {k : Vec3} (d : s.OnSlab hT k)
    (hT₁ : T ≤ 1) (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hScale : ℓ * D ^ p ≤ 1)
    (hRaw : TerminalMixedJetBound 0 T q p D A C (fun t x => s.residual t (s.flow 0 t x)))
    (hC : ∀ n, 0 ≤ C n) (n : ℕ) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) d.residualProfile ≤
      terminalLabelTimeSeminormCost C q n * A :=
  unweighted_timeJetSeminorm_le_of_labelMixedJetBound hT hT₁ hℓ hD hA hScale
    d.residualProfile d.residualProfile_value hRaw hC n

end InductiveEulerStage.OnSlab

end

end TorusEuler
