import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchySourceAssembly
import TorusEuler.HierarchyConcreteCompletion

/-! Fast source estimates for the finite lattice-twisted hierarchy. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- The scaled fast covector in the mixed-coordinate estimate. -/
def scaledPhaseCoefficientProfile (h : ℝ) (κ : VP) :
    HierarchyTwistedProfile T k (Vec3 →L[ℝ] ℝ) :=
  map (h⁻¹ • innerSL ℝ) κ

theorem scaledPhaseCoefficientProfile_apply (h : ℝ) (κ : VP) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (scaledPhaseCoefficientProfile h κ).val.val.val (t, x) =
      h⁻¹ • innerSL ℝ (κ.val.val.val (t, x)) := by
  have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  rw [scaledPhaseCoefficientProfile, map_val, HierarchyPeriodicProfile.map_val,
    HierarchySmoothProfile.map_apply _ _ hx]
  rfl

/-- The physical operator uses the fast derivative of the fixed-time label–phase slice. -/
theorem phaseAdv_apply_slice_fderiv (hT : 0 < T) (G M : MP) (κ Z Y : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    ((twistedHierarchyOperators hT G M κ).phaseAdv Z Y).val.val.val (t, x) =
      ⟪κ.val.val.val (t, x), Z.val.val.val (t, x)⟫_ℝ •
        fderiv ℝ (fun y => Y.val.val.val (t, y)) x (0, 1) := by
  have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val.val)
    Z.val.val Y.val.val).val (t, x) = _
  rw [HierarchySmoothProfile.advect_apply hT _ _ _ hx,
    HierarchySmoothProfile.phaseDirections_apply _ _ hx]
  have hY := ((HierarchySmoothProfile.smooth Y.val.val).differentiableOn (by simp)
    (t, x) hx).hasFDerivWithinAt
  let I := ContinuousLinearMap.inr ℝ ℝ (Vec3 × ℝ)
  have hi : HasFDerivAt (fun y : Vec3 × ℝ => (t, y)) I x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hslice : fderiv ℝ (fun y => Y.val.val.val (t, y)) x =
      (fderivWithin ℝ Y.val.val.val (hierarchyProfileSlab T) (t, x)).comp I :=
    (hY.comp_hasFDerivAt x hi (Filter.Eventually.of_forall fun _ => ⟨ht, mem_univ _⟩)).fderiv
  rw [hslice]
  change fderivWithin ℝ _ _ _ (0, 0, _) = _ • fderivWithin ℝ _ _ _ (0, 0, 1)
  rw [← map_smul]
  congr 1
  simp

private theorem finiteWordNorm_restrict_unweighted
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (f : HierarchyTwistedProfile T k E) :
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (weightedSlices A (fun _ => 1) f) ≤ unweightedSeminorm False ℓ h n hT f := by
  exact boundedWeightSeminorm_mono_time False ℓ h n hT hA
    (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T) (fun _ => 1) (C := 1) (by simp) f

set_option maxHeartbeats 3000000 in
/-- A bounded time weight on fast advection can be carried by the
differentiated profile. The advector and covector use full-slab seminorms. -/
theorem boundedWeightSeminorm_phaseAdv_le (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ)
    (hT : 0 < T) (G M : MP) (κ Z Y : VP)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {B : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) :
    boundedWeightSeminorm False ℓ h n hT hA τ hτ
        ((twistedHierarchyOperators hT G M κ).phaseAdv Z Y) ≤
      hierarchyQuadraticConstant (Fin 4) n ^ 2 *
        unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) *
        unweightedSeminorm False ℓ h n hT Z *
        boundedWeightSeminorm False ℓ h (n + 1) hT hA τ hτ Y := by
  let D := hierarchyMixedDirection ℓ h
  let F := scaledPhaseCoefficientProfile h κ
  let κa : A → (Vec3 × ℝ) → Vec3 := fun t x => κ.val.val.val (t, x)
  let Za : A → (Vec3 × ℝ) → Vec3 := weightedSlices A (fun _ => 1) Z
  let Ya : A → (Vec3 × ℝ) → Vec3 := fun t x => Y.val.val.val (t, x)
  let Yτ : A → (Vec3 × ℝ) → Vec3 := weightedSlices A τ Y
  have h₁ : ∀ t ∈ A, ‖(1 : ℝ)‖ ≤ 1 := by simp
  have hκa (t : A) : ContDiff ℝ ∞ (κa t) :=
    HierarchySmoothProfile.contDiff_labelPhase_slice κ.val.val (hA t.property)
  have hYa (t : A) : ContDiff ℝ ∞ (Ya t) :=
    HierarchySmoothProfile.contDiff_labelPhase_slice Y.val.val (hA t.property)
  have hZa (t : A) (x : Vec3 × ℝ) : Za t x = Z.val.val.val (t, x) := one_smul ℝ _
  have hF : hierarchyScaledPhaseCoefficient h κa = weightedSlices A (fun _ => 1) F := by
    funext t x
    change h⁻¹ • innerSL ℝ (κ.val.val.val (t, x)) = (1 : ℝ) • F.val.val.val (t, x)
    rw [one_smul, scaledPhaseCoefficientProfile_apply h κ (hA t.property)]
  have hFb (w : List (Fin 4)) (_ : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      BddAbove (hierarchyJetValues False D w (hierarchyScaledPhaseCoefficient h κa)) := by
    rw [hF]
    exact hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w F hA (fun _ => 1) h₁
  have hZb (w : List (Fin 4)) (_ : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      BddAbove (hierarchyJetValues False D w Za) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w Z hA (fun _ => 1) h₁
  have hYb (w : List (Fin 4)) (_ : w ∈ hierarchyAdmissibleWords (Fin 4) (n + 1)) :
      BddAbove (hierarchyJetValues False D w Yτ) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w Y hA τ hτ
  have hFle : hierarchyFiniteWordNorm False D n (hierarchyScaledPhaseCoefficient h κa) ≤
      unweightedSeminorm False ℓ h n hT F := by
    rw [hF]
    exact finiteWordNorm_restrict_unweighted ℓ h n hT hA F
  have hFfreq : hierarchyFiniteWordNorm False D n (hierarchyScaledPhaseCoefficient h κa) ≤
      unweightedSeminorm False ℓ h n hT F * (1 : ℝ) ^ (3 / 2 : ℝ) := by
    simpa only [Real.one_rpow, mul_one] using hFle
  have hraw := hierarchyFastAdvection_le ℓ h hh n
    hκa (weightedSlices_smooth hA (fun _ => 1) Z) (weightedSlices_smooth hA τ Y)
    hFb hZb hYb hFfreq
  rw [Real.one_rpow, mul_one] at hraw
  have hweights := hierarchy_fastAdvection_timeFactors (fun _ : A => 1) (fun t => τ t)
    κa Za Ya (fun t => (hYa t).differentiable (by simp))
  simp only [one_smul, one_mul] at hweights
  change (fun (t : A) x => ⟪κa t x, Za t x⟫_ℝ • fderiv ℝ (Yτ t) x (0, 1)) =
    (fun (t : A) x => τ t • (⟪κa t x, Za t x⟫_ℝ • fderiv ℝ (Ya t) x (0, 1))) at hweights
  change hierarchyFiniteWordNorm False D n
    (fun t x => ⟪κa t x, Za t x⟫_ℝ • fderiv ℝ (Yτ t) x (0, 1)) ≤ _ at hraw
  have heq : weightedSlices A τ ((twistedHierarchyOperators hT G M κ).phaseAdv Z Y) =
      fun (t : A) x => τ t • (⟪κa t x, Za t x⟫_ℝ • fderiv ℝ (Ya t) x (0, 1)) := by
    funext t x
    change τ t • ((twistedHierarchyOperators hT G M κ).phaseAdv Z Y).val.val.val (t, x) = _
    rw [phaseAdv_apply_slice_fderiv hT G M κ Z Y (hA t.property), hZa]
  rw [hweights, ← heq] at hraw
  change hierarchyFiniteWordNorm False D n
    (weightedSlices A τ ((twistedHierarchyOperators hT G M κ).phaseAdv Z Y)) ≤ _
  refine hraw.trans ?_
  have hYnonneg : 0 ≤ hierarchyFiniteWordNorm False D (n + 1) Yτ :=
    apply_nonneg (boundedWeightSeminorm False ℓ h (n + 1) hT hA τ hτ) Y
  apply mul_le_mul_of_nonneg_right _ hYnonneg
  apply mul_le_mul_of_nonneg_left (finiteWordNorm_restrict_unweighted ℓ h n hT hA Z)
  exact mul_nonneg (sq_nonneg _) (apply_nonneg _ _)

/-- The full-time fast advection estimate for the actual profiles. -/
theorem unweightedSeminorm_phaseAdv_le (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ)
    (hT : 0 < T) (G M : MP) (κ Z Y : VP) :
    unweightedSeminorm False ℓ h n hT ((twistedHierarchyOperators hT G M κ).phaseAdv Z Y) ≤
      hierarchyQuadraticConstant (Fin 4) n ^ 2 *
        unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) *
        unweightedSeminorm False ℓ h n hT Z * unweightedSeminorm False ℓ h (n + 1) hT Y :=
  boundedWeightSeminorm_phaseAdv_le ℓ h hh n hT G M κ Z Y
    (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T) (fun _ => 1) (B := 1) (by simp)

/-- The actual weighted fast source bound, used in particular for the supplementary
interaction between a mean advector and a weighted oscillation. -/
theorem amplitudeSeminorm_phaseAdv_le (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ)
    (hT : 0 < T) (G M : MP) (κ Z Y : VP) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t) :
    amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
        ((twistedHierarchyOperators hT G M κ).phaseAdv Z Y) ≤
      hierarchyQuadraticConstant (Fin 4) n ^ 2 *
        unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) *
        unweightedSeminorm False ℓ h n hT Z *
        amplitudeSeminorm False ℓ h (n + 1) hT ht₀ htT γ hγ hpos Y :=
  boundedWeightSeminorm_phaseAdv_le ℓ h hh n hT G M κ Z Y
    (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹)
    (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec


private def meanOfPhaseTranslations (f : (Vec3 × ℝ) → Vec3) (x : Vec3 × ℝ) : Vec3 :=
  phaseMean (fun r => f (x + (0, r)))

private theorem phaseDirectionalDerivative_meanOfPhaseTranslations
    {f : (Vec3 × ℝ) → Vec3} (hf : ContDiff ℝ ∞ f) (d : Vec3 × ℝ) :
    phaseDirectionalDerivative (fun _ => d) (meanOfPhaseTranslations f) =
      meanOfPhaseTranslations (phaseDirectionalDerivative (fun _ => d) f) := by
  let F (x : Vec3 × ℝ) (r : ℝ) := f (x + (0, r))
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    hf.comp (contDiff_fst.add (contDiff_const.prodMk contDiff_snd))
  funext x
  have hD : fderiv ℝ (meanOfPhaseTranslations f) x =
      phaseMean (fun r => fderiv ℝ f (x + (0, r))) := by
    change fderiv ℝ (fun y => phaseMean (F y)) x = _
    rw [fderiv_phaseMean_eq_phaseMean_fderiv hF]
    simp only [F, fderiv_comp_add_right]
  let A : ((Vec3 × ℝ) →L[ℝ] Vec3) →L[ℝ] Vec3 :=
    ContinuousLinearMap.apply ℝ Vec3 d
  have hc : Continuous (fun r : ℝ => fderiv ℝ f (x + (0, r))) :=
    (hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_const.prodMk continuous_id))
  change fderiv ℝ (meanOfPhaseTranslations f) x d =
    phaseMean (fun r => fderiv ℝ f (x + (0, r)) d)
  rw [hD]
  exact (A.intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)).symm

private theorem phaseOperatorWord_meanOfPhaseTranslations
    {ι : Type*} (d : ι → Vec3 × ℝ) (w : List ι) {f : (Vec3 × ℝ) → Vec3}
    (hf : ContDiff ℝ ∞ f) :
    phaseOperatorWord (fun i _ => d i) w (meanOfPhaseTranslations f) =
      meanOfPhaseTranslations (phaseOperatorWord (fun i _ => d i) w f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [phaseOperatorWord, ih]
    exact phaseDirectionalDerivative_meanOfPhaseTranslations
      (contDiff_phaseOperatorWord (fun _ => contDiff_const) hf w) (d i)

private theorem weightedSlices_average_eq_meanOfPhaseTranslations (hT : 0 < T)
    (G M : MP) (κ f : VP) {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) (t : A) :
    weightedSlices A τ ((twistedHierarchyOperators hT G M κ).average f) t =
      meanOfPhaseTranslations (weightedSlices A τ f t) := by
  funext ⟨a, s⟩
  have hx : (t.val, a, s) ∈ hierarchyProfileSlab T := ⟨hA t.property, mem_univ _⟩
  change τ t • (HierarchySmoothProfile.profilePhaseAverage hT f.val.val).val (t, a, s) =
    phaseMean (fun r => τ t • f.val.val.val (t, (a, s) + (0, r)))
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT f.val.val hx, ← phaseMean_const_smul]
  let q (r : ℝ) := τ t • f.val.val.val (t, a, r)
  have hper : Function.Periodic q 1 := by
    intro r
    exact congrArg (τ t • ·) (HierarchyPeriodicProfile.phasePeriodic f.val t a r)
  have heq : (fun r : ℝ => τ t • f.val.val.val (t, (a, s) + (0, r))) =
      fun r => q (r + s) := by
    funext r
    change τ t • f.val.val.val (t, a + 0, s + r) =
      τ t • f.val.val.val (t, a, r + s)
    rw [add_zero, add_comm s r]
  rw [heq]
  change phaseMean q = phaseMean (fun r => q (r + s))
  unfold phaseMean
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ) s] using (hper.intervalIntegral_add_eq s 0).symm

set_option maxHeartbeats 3000000 in
/-- Phase averaging is contractive on the finite supremum seminorm, with
any bounded time-only weight on the chosen slab. -/
theorem boundedWeightSeminorm_average_le (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    (G M : MP) (κ f : VP) {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {B : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) :
    boundedWeightSeminorm False ℓ h n hT hA τ hτ
      ((twistedHierarchyOperators hT G M κ).average f) ≤
      boundedWeightSeminorm False ℓ h n hT hA τ hτ f := by
  let D := hierarchyMixedDirection ℓ h
  let F := weightedSlices A τ f
  let Fbar := weightedSlices A τ ((twistedHierarchyOperators hT G M κ).average f)
  change hierarchyFiniteWordNorm False D n Fbar ≤ hierarchyFiniteWordNorm False D n F
  unfold hierarchyFiniteWordNorm
  refine Finset.sum_le_sum fun w _ => ?_
  have hb := hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w f hA τ hτ
  refine csSup_le (s := hierarchyJetValues False D w Fbar) ⟨0, Or.inl rfl⟩ ?_
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hfalse, _⟩)
  · exact le_csSup hb (Or.inl rfl)
  · have hword : phaseOperatorWord D w (Fbar t) =
        meanOfPhaseTranslations (phaseOperatorWord D w (F t)) := by
      change phaseOperatorWord D w
        (weightedSlices A τ ((twistedHierarchyOperators hT G M κ).average f) t) = _
      rw [weightedSlices_average_eq_meanOfPhaseTranslations hT G M κ f hA τ t]
      exact phaseOperatorWord_meanOfPhaseTranslations (fun i => D i 0) w
        (weightedSlices_smooth hA τ f t)
    rw [hword]
    refine norm_phaseMean_le fun s _ => ?_
    exact le_csSup hb (Or.inr (Or.inl ⟨t, x + (0, s), rfl⟩))
  · exact hfalse.elim

/-- Unweighted finite supremum seminorms decrease under phase averaging. -/
theorem unweightedSeminorm_average_le (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    (G M : MP) (κ f : VP) :
    unweightedSeminorm False ℓ h n hT ((twistedHierarchyOperators hT G M κ).average f) ≤
      unweightedSeminorm False ℓ h n hT f :=
  boundedWeightSeminorm_average_le ℓ h n hT G M κ f
    (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T) (fun _ => 1) (B := 1) (by simp)

/-- The amplitude-weighted finite supremum seminorm decreases under phase averaging. -/
theorem amplitudeSeminorm_average_le (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    (G M : MP) (κ f : VP) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t) :
    amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
        ((twistedHierarchyOperators hT G M κ).average f) ≤
      amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos f :=
  boundedWeightSeminorm_average_le ℓ h n hT G M κ f (Icc_subset_Icc_left ht₀)
    (fun t => (γ t)⁻¹)
    (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec

/-- The centered fast completion product has the two amplitude-weighted
factors in the oscillatory source recurrence. -/
theorem amplitudeSeminorm_centered_phaseAdv_le_of_inactive
    (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ) (hT : 0 < T) (G M : MP) (κ C Y : VP)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, C.val.val.val (t, x) = 0) :
    let A := twistedHierarchyOperators hT G M κ
    let F := A.phaseAdv C Y
    amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos (F - A.average F) ≤
      (2 * hierarchyQuadraticConstant (Fin 4) n ^ 2) *
        unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) *
        amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos C *
        amplitudeSeminorm False ℓ h (n + 1) hT ht₀ htT γ hγ hpos Y := by
  let A := twistedHierarchyOperators hT G M κ
  let F := A.phaseAdv C Y
  let N := amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos (k := k) (E := Vec3)
  let N₁ := amplitudeSeminorm False ℓ h (n + 1) hT ht₀ htT γ hγ hpos (k := k) (E := Vec3)
  let NF := unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ)
  let K := hierarchyQuadraticConstant (Fin 4) n ^ 2
  have hc := unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h n hT
    ht₀ htT γ hγ hpos hγle C hzero
  have hF : N F ≤ K * NF * N C * N₁ Y := by
    refine (amplitudeSeminorm_phaseAdv_le ℓ h hh n hT G M κ C Y ht₀ htT γ hγ hpos).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (mul_nonneg (sq_nonneg _) (apply_nonneg _ _)))
      (apply_nonneg _ _)
  have ha : N (A.average F) ≤ N F :=
    amplitudeSeminorm_average_le ℓ h n hT G M κ F ht₀ htT γ hγ hpos
  change N (F - A.average F) ≤ 2 * K * NF * N C * N₁ Y
  calc
    _ ≤ N F + N (A.average F) := map_sub_le_add N _ _
    _ ≤ (K * NF * N C * N₁ Y) + (K * NF * N C * N₁ Y) := add_le_add hF (ha.trans hF)
    _ = _ := by ring

end

end TorusEuler.HierarchyTwistedProfile
