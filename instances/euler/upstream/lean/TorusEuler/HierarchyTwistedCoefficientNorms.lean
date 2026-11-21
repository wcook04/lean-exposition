import TorusEuler.HierarchyTwistedFastSourceBounds
import TorusEuler.HierarchyLinearRelayBounds
import TorusEuler.ParentCoframeEstimates

/-! Exact finite seminorm bounds for the scaled transported phase coefficient. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- A normalized label coefficient bound controls the exact mixed-word
seminorm of its phase-independent twisted realization. -/
theorem unweightedSeminorm_le_of_labelCoefficientJets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hT : 0 < T)
    (ℓ h : ℝ) (n : ℕ) {B : ℝ} (f : HierarchyTwistedProfile T k E)
    (c : Icc (0 : ℝ) T → Vec3 → E)
    (hval : ∀ (t : Icc (0 : ℝ) T) (x : Vec3 × ℝ), f.val.val.val (t, x) = c t x.1)
    (hc : HierarchyRelayCoefficientJets ℓ h n B c) :
    unweightedSeminorm False ℓ h n hT f ≤
      (hierarchyAdmissibleWords (Fin 4) n).card * B := by
  let S := Icc (0 : ℝ) T
  have heq : weightedSlices S (fun _ => 1) f = fun t x => c t x.1 := by
    funext t x
    change (1 : ℝ) • f.val.val.val (t, x) = c t x.1
    rw [one_smul, hval]
  change hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
    (weightedSlices S (fun _ => 1) f) ≤ _
  rw [heq]
  exact hierarchyFiniteWordNorm_sup_le hc.2.1 hc.2.2

set_option maxHeartbeats 1000000 in
/-- The normalized covector jets imply the exact `h⁻¹κ` coefficient budget
with one fixed parent power and the fast frequency factor `freq^(3/2)`. -/
theorem unweightedSeminorm_scaledPhaseCoefficient_le_of_normalizedJets
    (hT : 0 < T) (κ : VP) (hκ : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    {ℓ h D freq : ℝ} (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hscale : ℓ * D ^ (7 : ℕ) ≤ 1)
    (hfreq : 0 < freq) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (n : ℕ) (C : ℕ → ℝ) (hC : ∀ j ≤ n, 0 ≤ C j)
    (hjet : ∀ j ≤ n, ∀ t ∈ Icc 0 T, ∀ a,
      ‖iteratedFDeriv ℝ j (fun b => freq⁻¹ • κ.val.val.val (t, b, 0)) a‖ ≤
        C j * D ^ (7 * j + 2)) :
    unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) ≤
      ((hierarchyAdmissibleWords (Fin 4) n).card *
        (∑ j ∈ Finset.range (n + 1), C j)) * D ^ 2 * freq ^ (3 / 2 : ℝ) := by
  let S := Icc (0 : ℝ) T
  let q (t : S) (a : Vec3) := freq⁻¹ • κ.val.val.val (t, a, 0)
  let factor := freq ^ (3 / 2 : ℝ)
  let L : Vec3 →L[ℝ] (Vec3 →L[ℝ] ℝ) := (h⁻¹ * freq) • innerSL ℝ
  let c (t : S) := L ∘ q t
  have hwidth' : h⁻¹ * freq = factor := by
    rw [hWidth, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hfreq.le, inv_inv]
    change freq ^ (1 / 2 : ℝ) * freq = freq ^ (3 / 2 : ℝ)
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hfreq, Real.rpow_one]
  have hfactor : 0 ≤ factor := Real.rpow_nonneg hfreq.le _
  have hL : ‖L‖ ≤ factor := by
    apply L.opNorm_le_bound hfactor
    intro v
    change ‖(h⁻¹ * freq) • innerSL ℝ v‖ ≤ factor * ‖v‖
    rw [norm_smul, hwidth', Real.norm_eq_abs, abs_of_nonneg hfactor, innerSL_apply_norm]
  have hq (t : S) : ContDiff ℝ ∞ (q t) :=
    ((HierarchySmoothProfile.contDiff_labelPhase_slice κ.val.val t.property).comp
      (contDiff_id.prodMk contDiff_const)).const_smul _
  have hc (t : S) : ContDiff ℝ ∞ (c t) := L.contDiff.comp (hq t)
  have hcv (t : S) (x : Vec3 × ℝ) :
      (scaledPhaseCoefficientProfile h κ).val.val.val (t, x) = c t x.1 := by
    rw [scaledPhaseCoefficientProfile_apply h κ t.property x]
    have hx : (t.val, x.1, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨t.property, mem_univ _⟩
    have hphase : κ.val.val.val (t, x) = κ.val.val.val (t, x.1, 0) := by
      rcases x with ⟨a, s⟩
      exact hκ (t.val, a, 0) hx s
    rw [hphase]
    change _ = (h⁻¹ * freq) • ((innerSL ℝ) (freq⁻¹ • κ.val.val.val (t, x.1, 0)))
    rw [map_smul, smul_smul]
    rw [mul_assoc, mul_inv_cancel₀ hfreq.ne', mul_one]
  have hjetc (t : S) (j : ℕ) (hj : j ≤ n) (a : Vec3) :
      ‖iteratedFDeriv ℝ j (c t) a‖ ≤ C j * (D ^ 2 * factor) * D ^ (7 * j) := by
    calc
      _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (q t) a‖ :=
        L.norm_iteratedFDeriv_comp_left (hq t).contDiffAt (by simp)
      _ ≤ factor * (C j * D ^ (7 * j + 2)) :=
        mul_le_mul hL (hjet j hj t t.property a) (norm_nonneg _) hfactor
      _ = _ := by rw [pow_add]; ring
  have hJ := HierarchyRelayCoefficientJets.of_parent_power_bound (h := h) (q := 7)
    hℓ hD (mul_nonneg (sq_nonneg _) hfactor) hscale hc hC hjetc
  refine (unweightedSeminorm_le_of_labelCoefficientJets hT ℓ h n
    (scaledPhaseCoefficientProfile h κ) c hcv hJ).trans_eq ?_
  dsimp only [factor]
  ring

/-- Instantiation of the fast coefficient budget on the transported parent
covector, using the actual central-length normalization at activation. -/
theorem exists_transported_scaledPhaseCoefficient_bound (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ} (hT : 0 < T), T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j) →
        ∀ (k : Vec3) (κ : HierarchyTwistedProfile T k Vec3),
          (∀ t ∈ Icc 0 T, ∀ a s, κ.val.val.val (t, a, s) = labelWaveVector X 0 a k t) →
          ∀ {freq t₀ ℓ h : ℝ}, 0 < freq → t₀ ∈ Icc 0 T →
          ‖labelWaveVector X 0 0 k t₀‖ = freq → 0 ≤ ℓ → ℓ * D ^ (7 : ℕ) ≤ 1 →
          h = freq ^ (-1 / 2 : ℝ) → ∀ n,
          unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) ≤
            K n * D ^ 2 * freq ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hjet⟩ := exists_parent_coefficientJetBounds R hR
  let K (n : ℕ) := (hierarchyAdmissibleWords (Fin 4) n).card *
    (∑ j ∈ Finset.range (n + 1), C j)
  refine ⟨K, fun n => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun j _ => hC j)), ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hG hUjet k κ hκ freq t₀ ℓ h hfreq ht₀ hcenter hℓ hscale hw n
  have hPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val := by
    rintro ⟨t, a, s⟩ ht r
    have htime : t ∈ Icc 0 T := ht.1
    rw [show κ.val.val.val (t, a, r) = labelWaveVector X 0 a k t from hκ t htime a r,
      show κ.val.val.val (t, a, s) = labelWaveVector X 0 a k t from hκ t htime a s]
  refine unweightedSeminorm_scaledPhaseCoefficient_le_of_normalizedJets hT κ hPhase hℓ
    (zero_le_one.trans hD) hscale hfreq hw n C (fun j _ => hC j) ?_
  intro j _ t ht a
  have heq : (fun b => freq⁻¹ • κ.val.val.val (t, b, 0)) =
      fun b => freq⁻¹ • labelWaveVector X 0 b k t := by
    funext b
    rw [hκ t ht b 0]
  rw [heq]
  exact (hjet hT hT₁ hD hX hU hper hF hG hUjet k hfreq ht₀ hcenter j t ht a).2.2.2.2.1

end

end TorusEuler.HierarchyTwistedProfile
