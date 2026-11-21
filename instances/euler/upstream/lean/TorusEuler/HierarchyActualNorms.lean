import TorusEuler.HierarchyLevelBounds
import TorusEuler.HierarchyProductEstimates
import TorusEuler.PeriodicLift
import TorusEuler.HierarchyTwistedProfiles
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Data.Real.Pointwise

/-! The finite mixed-coordinate seminorms of Appendix D. The time
weight is applied after restricting time, before any spatial derivative. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace NNReal Pointwise

namespace TorusEuler

section WordSeminorm

variable {ι T U E M : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup M] [Module ℝ M]

omit [Fintype ι] [LinearOrder ι] in
private theorem actualWord_zero (D : ι → U → U) (w : List ι) :
    phaseOperatorWord D w (0 : U → E) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [phaseOperatorWord, ih]
    funext x
    change fderiv ℝ (fun _ : U => (0 : E)) x (D i x) = 0
    simp

omit [Fintype ι] [LinearOrder ι] in
private theorem actualWord_add {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    {f g : U → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List ι) (x : U) :
    phaseOperatorWord D w (f + g) x = phaseOperatorWord D w f x + phaseOperatorWord D w g x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    change fderiv ℝ (phaseOperatorWord D w (f + g)) x (D i x) = _
    rw [show phaseOperatorWord D w (f + g) =
      phaseOperatorWord D w f + phaseOperatorWord D w g from funext ih,
      fderiv_add ((contDiff_phaseOperatorWord hD hf w).differentiable (by simp) x)
        ((contDiff_phaseOperatorWord hD hg w).differentiable (by simp) x)]
    rfl

omit [Fintype ι] [LinearOrder ι] in
/-- Summing two smooth fields adds the supremum bounds of the same derivative word. -/
theorem actualJetValues_add_le (holder : Prop) {D : ι → U → U}
    (hD : ∀ i, ContDiff ℝ ∞ (D i)) (w : List ι) {f g : T → U → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hbdf : BddAbove (hierarchyJetValues holder D w f))
    (hbdg : BddAbove (hierarchyJetValues holder D w g)) :
    sSup (hierarchyJetValues holder D w (f + g)) ≤
      sSup (hierarchyJetValues holder D w f) + sSup (hierarchyJetValues holder D w g) := by
  let F := sSup (hierarchyJetValues holder D w f)
  let G := sSup (hierarchyJetValues holder D w g)
  have hF : 0 ≤ F := le_csSup hbdf (Or.inl rfl)
  have hG : 0 ≤ G := le_csSup hbdg (Or.inl rfl)
  refine csSup_le (s := hierarchyJetValues holder D w (f + g)) ⟨0, Or.inl rfl⟩ ?_
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, t, x, y, rfl⟩)
  · exact add_nonneg hF hG
  · change ‖phaseOperatorWord D w (f t + g t) x‖ ≤ F + G
    rw [actualWord_add hD (hf t) (hg t)]
    exact (norm_add_le _ _).trans (add_le_add
      (le_csSup hbdf (Or.inr (Or.inl ⟨t, x, rfl⟩)))
      (le_csSup hbdg (Or.inr (Or.inl ⟨t, x, rfl⟩))))
  · change ‖phaseOperatorWord D w (f t + g t) x - phaseOperatorWord D w (f t + g t) y‖ /
      Real.sqrt (dist x y) ≤ F + G
    rw [actualWord_add hD (hf t) (hg t), actualWord_add hD (hf t) (hg t), show
      phaseOperatorWord D w (f t) x + phaseOperatorWord D w (g t) x -
        (phaseOperatorWord D w (f t) y + phaseOperatorWord D w (g t) y) =
        (phaseOperatorWord D w (f t) x - phaseOperatorWord D w (f t) y) +
          (phaseOperatorWord D w (g t) x - phaseOperatorWord D w (g t) y) by abel]
    calc
      _ ≤ (‖phaseOperatorWord D w (f t) x - phaseOperatorWord D w (f t) y‖ +
            ‖phaseOperatorWord D w (g t) x - phaseOperatorWord D w (g t) y‖) /
            Real.sqrt (dist x y) :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _)
      _ ≤ F + G := by
        rw [add_div]
        exact add_le_add (le_csSup hbdf (Or.inr (Or.inr ⟨hH, t, x, y, rfl⟩)))
          (le_csSup hbdg (Or.inr (Or.inr ⟨hH, t, x, y, rfl⟩)))

omit [Fintype ι] [LinearOrder ι] in
/-- Scalar multiplication scales each actual derivative supremum by the scalar norm. -/
theorem actualJetValues_smul (holder : Prop) {D : ι → U → U}
    (hD : ∀ i, ContDiff ℝ ∞ (D i)) (w : List ι) {f : T → U → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (c : ℝ) :
    hierarchyJetValues holder D w (c • f) = ‖c‖ • hierarchyJetValues holder D w f := by
  have hword (t : T) (x : U) :
      phaseOperatorWord D w ((c • f) t) x = c • phaseOperatorWord D w (f t) x :=
    phaseOperatorWord_const_smul hD (hf t) c w x
  ext r
  change r ∈ hierarchyJetValues holder D w (c • f) ↔
    r ∈ (fun q : ℝ => ‖c‖ • q) '' hierarchyJetValues holder D w f
  constructor
  · rintro (rfl | ⟨t, x, rfl⟩ | ⟨hH, t, x, y, rfl⟩)
    · exact ⟨0, Or.inl rfl, mul_zero _⟩
    · exact ⟨_, Or.inr (Or.inl ⟨t, x, rfl⟩), by simp only [hword, norm_smul, smul_eq_mul]⟩
    · refine ⟨_, Or.inr (Or.inr ⟨hH, t, x, y, rfl⟩), ?_⟩
      simp only [hword, ← smul_sub, norm_smul, smul_eq_mul, mul_div_assoc]
  · rintro ⟨q, (rfl | ⟨t, x, rfl⟩ | ⟨hH, t, x, y, rfl⟩), rfl⟩
    · exact Or.inl (mul_zero _)
    · exact Or.inr (Or.inl ⟨t, x, by simp only [hword, norm_smul, smul_eq_mul]⟩)
    · refine Or.inr (Or.inr ⟨hH, t, x, y, ?_⟩)
      simp only [hword, ← smul_sub, norm_smul, smul_eq_mul, mul_div_assoc]

/-- Summing the exact real suprema of the finite derivative family gives a
seminorm whenever these measurements are bounded on the profile space. -/
noncomputable def hierarchyFiniteWordSeminorm (holder : Prop) (D : ι → U → U)
    (n : ℕ) (slice : M →ₗ[ℝ] (T → U → E)) (hD : ∀ i, ContDiff ℝ ∞ (D i))
    (hSmooth : ∀ f t, ContDiff ℝ ∞ (slice f t))
    (hBounded : ∀ f w, w ∈ hierarchyAdmissibleWords ι n →
      BddAbove (hierarchyJetValues holder D w (slice f))) : Seminorm ℝ M :=
  Seminorm.of (fun f => hierarchyFiniteWordNorm holder D n (slice f))
    (fun f g => by
      simp only [hierarchyFiniteWordNorm, map_add, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun w hw => actualJetValues_add_le holder hD w
        (hSmooth f) (hSmooth g) (hBounded f w hw) (hBounded g w hw))
    (fun c f => by
      simp only [hierarchyFiniteWordNorm, map_smul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [actualJetValues_smul holder hD w (hSmooth f) c, Real.sSup_smul_of_nonneg (norm_nonneg c)]
      rfl)

@[simp] theorem hierarchyFiniteWordSeminorm_apply (holder : Prop) (D : ι → U → U)
    (n : ℕ) (slice : M →ₗ[ℝ] (T → U → E)) (hD : ∀ i, ContDiff ℝ ∞ (D i))
    (hSmooth : ∀ f t, ContDiff ℝ ∞ (slice f t))
    (hBounded : ∀ f w, w ∈ hierarchyAdmissibleWords ι n →
      BddAbove (hierarchyJetValues holder D w (slice f))) (f : M) :
    hierarchyFiniteWordSeminorm holder D n slice hD hSmooth hBounded f =
      hierarchyFiniteWordNorm holder D n (slice f) := rfl

/-- Each actual pointwise mixed jet is controlled by the finite norm. -/
theorem norm_word_le_hierarchyFiniteWordNorm (holder : Prop) {D : ι → U → U}
    {n : ℕ} {f : T → U → E}
    (hb : ∀ v ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D v f))
    {w : List ι} (hw : w ∈ hierarchyAdmissibleWords ι n) (t : T) (x : U) :
    ‖phaseOperatorWord D w (f t) x‖ ≤ hierarchyFiniteWordNorm holder D n f := by
  refine (le_csSup (hb w hw) (Or.inr (Or.inl ⟨t, x, rfl⟩))).trans ?_
  exact Finset.single_le_sum (fun v hv => le_csSup (hb v hv) (Or.inl rfl)) hw

/-- A common bound on the pointwise mixed jets controls their exact sum
with only the number of admissible multi-indices as a factor. -/
theorem hierarchyFiniteWordNorm_sup_le {D : ι → U → U} {n : ℕ} {f : T → U → E}
    {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ w ∈ hierarchyAdmissibleWords ι n, ∀ t x,
      ‖phaseOperatorWord D w (f t) x‖ ≤ B) :
    hierarchyFiniteWordNorm False D n f ≤ (hierarchyAdmissibleWords ι n).card * B := by
  unfold hierarchyFiniteWordNorm
  calc
    _ ≤ ∑ _ ∈ hierarchyAdmissibleWords ι n, B := by
      refine Finset.sum_le_sum fun w hw => csSup_le
        (s := hierarchyJetValues False D w f) ⟨0, Or.inl rfl⟩ ?_
      rintro r (rfl | ⟨t, x, rfl⟩ | ⟨h, _⟩)
      · exact hB
      · exact hjets w hw t x
      · exact h.elim
    _ = _ := by simp

/-- Restricting the time parameter cannot increase the finite mixed norm. -/
theorem hierarchyFiniteWordNorm_restrict_time_le {S : Type*} (incl : S → T)
    (holder : Prop) {D : ι → U → U} {n : ℕ} {f : T → U → E}
    (hb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f)) :
    hierarchyFiniteWordNorm holder D n (f ∘ incl) ≤ hierarchyFiniteWordNorm holder D n f := by
  unfold hierarchyFiniteWordNorm
  refine Finset.sum_le_sum fun w hw => csSup_le
    (s := hierarchyJetValues holder D w (f ∘ incl)) ⟨0, Or.inl rfl⟩ ?_
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, t, x, y, rfl⟩)
  · exact le_csSup (hb w hw) (Or.inl rfl)
  · exact le_csSup (hb w hw) (Or.inr (Or.inl ⟨incl t, x, rfl⟩))
  · exact le_csSup (hb w hw) (Or.inr (Or.inr ⟨hH, incl t, x, y, rfl⟩))

/-- Every admissible mixed multi-index remains admissible at higher order. -/
theorem hierarchyAdmissibleWords_mono (ι : Type*) [Fintype ι] [LinearOrder ι] :
    Monotone (hierarchyAdmissibleWords ι) := by
  intro n m hnm w hw
  obtain ⟨hlen, hsorted⟩ := mem_hierarchyAdmissibleWords.mp hw
  exact mem_hierarchyAdmissibleWords.mpr ⟨hlen.trans hnm, hsorted⟩

/-- Adding higher orders can only increase the finite mixed norm. -/
theorem hierarchyFiniteWordNorm_mono_order (holder : Prop) {D : ι → U → U}
    {n m : ℕ} (hnm : n ≤ m) {f : T → U → E}
    (hb : ∀ w ∈ hierarchyAdmissibleWords ι m, BddAbove (hierarchyJetValues holder D w f)) :
    hierarchyFiniteWordNorm holder D n f ≤ hierarchyFiniteWordNorm holder D m f :=
  Finset.sum_le_sum_of_subset_of_nonneg (hierarchyAdmissibleWords_mono ι hnm)
    (fun w hw _ => le_csSup (hb w hw) (Or.inl rfl))

end WordSeminorm

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def hierarchyTwistedSliceInclusion : (Vec3 × ℝ) →L[ℝ] HierarchyProfilePoint :=
  inr ℝ ℝ (Vec3 × ℝ)

private theorem hierarchyTwistedSlice_hasFDerivAt (f : HierarchyTwistedProfile T k E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    HasFDerivAt (fun z => f.val.val.val (t, z))
      ((fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T) (t, x)).comp
        hierarchyTwistedSliceInclusion) x := by
  have hf := ((HierarchySmoothProfile.smooth f.val.val).differentiableOn (by simp)
    (t, x) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hi : HasFDerivAt (fun z : Vec3 × ℝ => (t, z)) hierarchyTwistedSliceInclusion x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact hf.comp_hasFDerivAt x hi (Filter.Eventually.of_forall fun _ => ⟨ht, mem_univ _⟩)

/-- The full label-phase derivative of a twisted profile, with time held fixed. -/
def hierarchyTwistedSliceDerivative (hT : 0 < T) : HierarchyTwistedProfile T k E →ₗ[ℝ]
    HierarchyTwistedProfile T k ((Vec3 × ℝ) →L[ℝ] E) :=
  (HierarchyTwistedProfile.map ((compL ℝ (Vec3 × ℝ) HierarchyProfilePoint E).flip
    hierarchyTwistedSliceInclusion)).comp (HierarchyTwistedProfile.derivative hT)

theorem hierarchyTwistedSliceDerivative_apply (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (hierarchyTwistedSliceDerivative hT f).val.val.val (t, x) =
      fderiv ℝ (fun z => f.val.val.val (t, z)) x := by
  have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  simp only [hierarchyTwistedSliceDerivative, LinearMap.comp_apply, HierarchyTwistedProfile.map_val,
    HierarchyPeriodicProfile.map_val, HierarchySmoothProfile.map_apply _ _ hx,
    HierarchyTwistedProfile.derivative_val, HierarchyPeriodicProfile.derivative_val,
    HierarchySmoothProfile.derivative_apply _ _ hx]
  exact (hierarchyTwistedSlice_hasFDerivAt f ht x).fderiv.symm

/-- Mixed coordinate words act linearly and preserve smooth lattice-twisted profiles. -/
def hierarchyTwistedMixedWord (hT : 0 < T) (ℓ h : ℝ) : List (Fin 4) →
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k E
  | [] => LinearMap.id
  | i :: w => (HierarchyTwistedProfile.map (ContinuousLinearMap.apply ℝ E
      (hierarchyMixedDirection ℓ h i 0))).comp
      ((hierarchyTwistedSliceDerivative hT).comp (hierarchyTwistedMixedWord hT ℓ h w))

theorem hierarchyTwistedMixedWord_apply (hT : 0 < T) (ℓ h : ℝ) (w : List (Fin 4))
    (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (hierarchyTwistedMixedWord hT ℓ h w f).val.val.val (t, x) =
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t, z)) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    rw [hierarchyTwistedMixedWord, LinearMap.comp_apply, LinearMap.comp_apply,
      HierarchyTwistedProfile.map_val, HierarchyPeriodicProfile.map_val,
      HierarchySmoothProfile.map_apply _ _ hx]
    change (hierarchyTwistedSliceDerivative hT (hierarchyTwistedMixedWord hT ℓ h w f)).val.val.val
      (t, x) (hierarchyMixedDirection ℓ h i 0) = _
    rw [hierarchyTwistedSliceDerivative_apply hT _ ht x, funext ih]
    rfl

/-- Smooth twisted profiles are uniformly bounded on the closed time slab. -/
theorem hierarchyTwistedProfile_exists_norm_bound (f : HierarchyTwistedProfile T k E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ x : Vec3 × ℝ, ‖f.val.val.val (t, x)‖ ≤ M := by
  let K : Set HierarchyProfilePoint := Icc 0 T ×ˢ (centeredCell ×ˢ Icc 0 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_centeredCell.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((HierarchySmoothProfile.smooth f.val.val).continuousOn.mono
      (prod_subset_prod_right (subset_univ _)))
  refine ⟨max M 0, le_max_right _ _, fun t ht ⟨a, s⟩ => ?_⟩
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  let a₀ := a - latticeVector n
  let s₀ := s - ⟪k, latticeVector n⟫_ℝ
  have htw : f.val.val.val (t, a, s) = f.val.val.val (t, a₀, s₀) := by
    simpa only [a₀, s₀, sub_add_cancel] using HierarchyTwistedProfile.twistedSlice f t a₀ s₀ n
  have hper : f.val.val.val (t, a₀, Int.fract s₀) = f.val.val.val (t, a₀, s₀) := by
    simpa only [Int.fract, mul_one] using
      (HierarchyPeriodicProfile.phasePeriodic f.val t a₀).sub_int_mul_eq (x := s₀) ⌊s₀⌋
  rw [htw, ← hper]
  exact (hM (t, a₀, Int.fract s₀) ⟨ht, hn, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩).trans
    (le_max_left _ _)

theorem hierarchyTwistedMixedWord_exists_norm_bound (hT : 0 < T) (ℓ h : ℝ)
    (w : List (Fin 4)) (f : HierarchyTwistedProfile T k E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ x,
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t, z)) x‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := hierarchyTwistedProfile_exists_norm_bound (hierarchyTwistedMixedWord hT ℓ h w f)
  exact ⟨M, hM, fun t ht x => hierarchyTwistedMixedWord_apply hT ℓ h w f ht x ▸ hb t ht x⟩

theorem hierarchyTwistedProfile_exists_sliceLipschitz (hT : 0 < T) (f : HierarchyTwistedProfile T k E) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzWith K (fun z : Vec3 × ℝ => f.val.val.val (t, z)) := by
  obtain ⟨M, hM, hb⟩ := hierarchyTwistedProfile_exists_norm_bound (hierarchyTwistedSliceDerivative hT f)
  refine ⟨⟨M, hM⟩, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hierarchyTwistedSlice_hasFDerivAt f ht x).differentiableAt) (fun x => ?_)⟩
  have h := hb t ht x
  rw [hierarchyTwistedSliceDerivative_apply hT f ht x] at h
  exact h

/-- Each mixed coordinate jet has a uniform value and half-Hölder bound. -/
theorem hierarchyTwistedMixedWord_exists_halfHolder_bound (hT : 0 < T) (ℓ h : ℝ)
    (w : List (Fin 4)) (f : HierarchyTwistedProfile T k E) :
    let J (t : ℝ) := phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t, z))
    ∃ M : ℝ, 0 ≤ M ∧ (∀ t ∈ Icc 0 T, ∀ x, ‖J t x‖ ≤ M) ∧
      (∀ t ∈ Icc 0 T, ∀ x y, ‖J t x - J t y‖ ≤ M * Real.sqrt (dist x y)) := by
  let g := hierarchyTwistedMixedWord hT ℓ h w f
  obtain ⟨A, hA, hv⟩ := hierarchyTwistedProfile_exists_norm_bound g
  obtain ⟨B, hB, hd⟩ := hierarchyTwistedProfile_exists_norm_bound (hierarchyTwistedSliceDerivative hT g)
  refine ⟨max A (Real.sqrt (2 * A * B)), hA.trans (le_max_left _ _), ?_, ?_⟩
  · intro t ht x
    change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t, z)) x‖ ≤ _
    rw [← hierarchyTwistedMixedWord_apply hT ℓ h w f ht x]
    exact (hv t ht x).trans (le_max_left _ _)
  · intro t ht x y
    change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t, z)) x -
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t, z)) y‖ ≤ _
    rw [← hierarchyTwistedMixedWord_apply hT ℓ h w f ht x,
      ← hierarchyTwistedMixedWord_apply hT ℓ h w f ht y]
    have hb (z : Vec3 × ℝ) : ‖fderiv ℝ (fun u => g.val.val.val (t, u)) z‖ ≤ B := by
      rw [← hierarchyTwistedSliceDerivative_apply hT g ht z]
      exact hd t ht z
    have hdiff : ‖g.val.val.val (t, x) - g.val.val.val (t, y)‖ ≤ B * dist x y := by
      simpa only [dist_eq_norm] using
        (convex_univ : Convex ℝ (Set.univ : Set (Vec3 × ℝ))).norm_image_sub_le_of_norm_fderiv_le
          (fun z _ => (hierarchyTwistedSlice_hasFDerivAt g ht z).differentiableAt)
          (fun z _ => hb z) (Set.mem_univ y) (Set.mem_univ x)
    have hsum : ‖g.val.val.val (t, x) - g.val.val.val (t, y)‖ ≤ 2 * A := by
      rw [two_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hv t ht x) (hv t ht y))
    have hsq : ‖g.val.val.val (t, x) - g.val.val.val (t, y)‖ ^ 2 ≤ (2 * A * B) * dist x y := by
      rw [sq, mul_assoc]
      exact mul_le_mul hsum hdiff (norm_nonneg _) (by positivity)
    have hhold : ‖g.val.val.val (t, x) - g.val.val.val (t, y)‖ ≤
        Real.sqrt (2 * A * B) * Real.sqrt (dist x y) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.le_sqrt_of_sq_le hsq
    exact hhold.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

/-- A bounded time-only multiplier preserves the boundedness of all samples
used for the finite norm, over any subset of the closed time slab. -/
theorem hierarchyTwistedMixedWord_bddAbove_weighted (hT : 0 < T) (ℓ h : ℝ)
    (holder : Prop) (w : List (Fin 4)) (f : HierarchyTwistedProfile T k E)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {B : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) :
    BddAbove (hierarchyJetValues holder (hierarchyMixedDirection ℓ h) w
      (fun (t : A) x => τ (t : ℝ) • f.val.val.val ((t : ℝ), x))) := by
  obtain ⟨M, hM, hsup, hhold⟩ := hierarchyTwistedMixedWord_exists_halfHolder_bound hT ℓ h w f
  let D := hierarchyMixedDirection ℓ h
  let J (t : A) := phaseOperatorWord D w (fun z => f.val.val.val ((t : ℝ), z))
  have heq (t : A) (x : Vec3 × ℝ) :
      phaseOperatorWord D w (fun z => τ (t : ℝ) • f.val.val.val ((t : ℝ), z)) x =
        τ (t : ℝ) • J t x := by
    have hs : ContDiff ℝ ∞ (fun z : Vec3 × ℝ => f.val.val.val ((t : ℝ), z)) :=
      contDiffOn_univ.mp ((HierarchySmoothProfile.smooth f.val.val).comp
        (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun _ _ => ⟨hA t.property, mem_univ _⟩))
    exact phaseOperatorWord_const_smul (fun _ => contDiff_const) hs _ w x
  refine ⟨max B 0 * M, ?_⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨_, t, x, y, rfl⟩)
  · exact mul_nonneg (le_max_right _ _) hM
  · rw [heq, norm_smul]
    exact mul_le_mul ((hτ t t.property).trans (le_max_left _ _))
      (hsup t (hA t.property) x) (norm_nonneg _) (le_max_right _ _)
  · by_cases hxy : x = y
    · subst y
      simpa only [sub_self, norm_zero, zero_div] using mul_nonneg (le_max_right B 0) hM
    · apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).2
      rw [heq, heq, ← smul_sub, norm_smul, mul_assoc]
      exact mul_le_mul ((hτ t t.property).trans (le_max_left _ _))
        (hhold t (hA t.property) x y) (norm_nonneg _) (le_max_right _ _)

end


namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate the profile at times in `A`, with a scalar multiplier depending
only on time. Using inverse amplitude here leaves label and phase orders intact. -/
def weightedSlices (A : Set ℝ) (τ : ℝ → ℝ) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] (A → Vec3 × ℝ → E) where
  toFun f t x := τ t • f.val.val.val (t, x)
  map_add' f g := by
    ext t x
    change τ t • (f.val.val.val (t, x) + g.val.val.val (t, x)) = _
    exact smul_add _ _ _
  map_smul' c f := by
    ext t x
    change τ t • c • f.val.val.val (t, x) = c • τ t • f.val.val.val (t, x)
    rw [smul_comm]

theorem weightedSlices_smooth {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ)
    (f : HierarchyTwistedProfile T k E) (t : A) :
    ContDiff ℝ ∞ (weightedSlices A τ f t) := by
  have h := contDiffOn_univ.mp ((HierarchySmoothProfile.smooth f.val.val).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => ⟨hA t.property, mem_univ _⟩))
  exact h.const_smul (τ t)

/-- The actual Appendix D mixed-word seminorm of a lattice-twisted profile.
The time set can be either the full slab or the closed positive-amplitude interval. -/
noncomputable def actualSeminorm (holder : Prop) (ℓ h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ)
    (hBounded : ∀ (f : HierarchyTwistedProfile T k E) w,
      w ∈ hierarchyAdmissibleWords (Fin 4) n →
      BddAbove (hierarchyJetValues holder (hierarchyMixedDirection ℓ h) w (weightedSlices A τ f))) :
    Seminorm ℝ (HierarchyTwistedProfile T k E) :=
  hierarchyFiniteWordSeminorm holder (hierarchyMixedDirection ℓ h) n (weightedSlices A τ)
    (fun _ => contDiff_const) (weightedSlices_smooth hA τ) hBounded

@[simp] theorem actualSeminorm_apply (holder : Prop) (ℓ h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ)
    (hBounded : ∀ (f : HierarchyTwistedProfile T k E) w,
      w ∈ hierarchyAdmissibleWords (Fin 4) n →
      BddAbove (hierarchyJetValues holder (hierarchyMixedDirection ℓ h) w (weightedSlices A τ f)))
    (f : HierarchyTwistedProfile T k E) :
    actualSeminorm holder ℓ h n hA τ hBounded f =
      hierarchyFiniteWordNorm holder (hierarchyMixedDirection ℓ h) n (weightedSlices A τ f) := rfl

/-- On a twisted profile every mixed jet is bounded on the slab, so any
bounded time multiplier gives a genuine real-valued finite seminorm. -/
noncomputable def boundedWeightSeminorm (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {B : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) : Seminorm ℝ (HierarchyTwistedProfile T k E) :=
  actualSeminorm holder ℓ h n hA τ fun f w _ =>
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w f hA τ hτ

@[simp] theorem boundedWeightSeminorm_apply (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {B : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) (f : HierarchyTwistedProfile T k E) :
    boundedWeightSeminorm holder ℓ h n hT hA τ hτ f =
      hierarchyFiniteWordNorm holder (hierarchyMixedDirection ℓ h) n (weightedSlices A τ f) := rfl

/-- Restricting to a smaller time domain lowers a fixed-weight seminorm. -/
theorem boundedWeightSeminorm_mono_time (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    {A B : Set ℝ} (hAB : A ⊆ B) (hB : B ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ}
    (hτ : ∀ t ∈ B, ‖τ t‖ ≤ C) (f : HierarchyTwistedProfile T k E) :
    boundedWeightSeminorm holder ℓ h n hT (hAB.trans hB) τ (fun t ht => hτ t (hAB ht)) f ≤
      boundedWeightSeminorm holder ℓ h n hT hB τ hτ f :=
  hierarchyFiniteWordNorm_restrict_time_le (fun t : A => (⟨t, hAB t.property⟩ : B)) holder
    (f := weightedSlices B τ f) (fun w _ =>
      hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w f hB τ hτ)

/-- The actual fixed-weight seminorm is monotone in derivative order. -/
theorem boundedWeightSeminorm_mono_order (holder : Prop) (ℓ h : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (hT : 0 < T) {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {B : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) (f : HierarchyTwistedProfile T k E) :
    boundedWeightSeminorm holder ℓ h n hT hA τ hτ f ≤
      boundedWeightSeminorm holder ℓ h m hT hA τ hτ f :=
  hierarchyFiniteWordNorm_mono_order holder hnm
    (f := weightedSlices A τ f) (fun w _ =>
      hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w f hA τ hτ)

/-- The time multipliers of a bilinear interaction can be placed on its
factors. This covers active weighted products and full-slab unweighted products. -/
theorem boundedWeightSeminorm_bilinear_le
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G)
    (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {A : Set ℝ} (hA : A ⊆ Icc 0 T)
    (τf τg τfg : ℝ → ℝ) {Cf Cg Cfg : ℝ}
    (hf : ∀ t ∈ A, ‖τf t‖ ≤ Cf) (hg : ∀ t ∈ A, ‖τg t‖ ≤ Cg)
    (hfg : ∀ t ∈ A, ‖τfg t‖ ≤ Cfg) (hweight : ∀ t ∈ A, τfg t = τf t * τg t)
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F)
    (fg : HierarchyTwistedProfile T k G)
    (heq : ∀ t ∈ A, ∀ x : Vec3 × ℝ,
      fg.val.val.val (t, x) = B (f.val.val.val (t, x)) (g.val.val.val (t, x))) :
    boundedWeightSeminorm holder ℓ h n hT hA τfg hfg fg ≤
      (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n *
        (2 * ‖B‖ * boundedWeightSeminorm holder ℓ h n hT hA τf hf f *
          boundedWeightSeminorm holder ℓ h n hT hA τg hg g) := by
  let D := hierarchyMixedDirection ℓ h
  let u : A → Vec3 × ℝ → E := weightedSlices A τf f
  let v : A → Vec3 × ℝ → F := weightedSlices A τg g
  have hslice : weightedSlices A τfg fg = fun t x => B (u t x) (v t x) := by
    funext t x
    change τfg t • fg.val.val.val (t, x) =
      B (τf t • f.val.val.val (t, x)) (τg t • g.val.val.val (t, x))
    rw [hweight t t.property, heq t t.property]
    simp only [map_smul, smul_apply, smul_smul, mul_comm (τg t) (τf t)]
  change hierarchyFiniteWordNorm holder D n (weightedSlices A τfg fg) ≤ _
  rw [hslice]
  exact hierarchyFiniteWordNorm_bilinear_le B holder (D := D) (fun _ => contDiff_const) n
    (weightedSlices_smooth hA τf f) (weightedSlices_smooth hA τg g)
    (fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w f hA τf hf)
    (fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w g hA τg hg)

/-- The unweighted norm measures the entire time slab. -/
noncomputable def unweightedSeminorm (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) :
    Seminorm ℝ (HierarchyTwistedProfile T k E) :=
  boundedWeightSeminorm holder ℓ h n hT (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T)
    (fun _ => 1) (B := 1) (by simp)

theorem unweightedSeminorm_mono_order (holder : Prop) (ℓ h : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (hT : 0 < T) (f : HierarchyTwistedProfile T k E) :
    unweightedSeminorm holder ℓ h n hT f ≤ unweightedSeminorm holder ℓ h m hT f :=
  boundedWeightSeminorm_mono_order holder ℓ h hnm hT (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T)
    (fun _ => 1) (B := 1) (by simp) f

/-- The reciprocal of a positive continuous amplitude is bounded on every
nonempty compact subset of the active interval. -/
theorem inverse_amplitude_has_bound {A : Set ℝ} (hA : IsCompact A) (hne : A.Nonempty)
    {γ : ℝ → ℝ} (hγ : ContinuousOn γ A) (hpos : ∀ t ∈ A, 0 < γ t) :
    ∃ B : ℝ, ∀ t ∈ A, ‖(γ t)⁻¹‖ ≤ B := by
  obtain ⟨t, ht, hmin⟩ := hA.exists_isMinOn hne hγ
  refine ⟨(γ t)⁻¹, fun u hu => ?_⟩
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos u hu))]
  exact inv_anti₀ (hpos t ht) (hmin hu)

/-- The Appendix D seminorm with the reciprocal seed amplitude on the
closed interval `[t₀,T]`, where the seed is strictly positive. -/
noncomputable def amplitudeSeminorm (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t) :
    Seminorm ℝ (HierarchyTwistedProfile T k E) :=
  boundedWeightSeminorm holder ℓ h n hT (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹)
    (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec

@[simp] theorem amplitudeSeminorm_apply (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (f : HierarchyTwistedProfile T k E) :
    amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos f =
      hierarchyFiniteWordNorm holder (hierarchyMixedDirection ℓ h) n
        (weightedSlices (Icc t₀ T) (fun t => (γ t)⁻¹) f) := rfl

theorem amplitudeSeminorm_mono_order (holder : Prop) (ℓ h : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (f : HierarchyTwistedProfile T k E) :
    amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos f ≤
      amplitudeSeminorm holder ℓ h m hT ht₀ htT γ hγ hpos f :=
  boundedWeightSeminorm_mono_order holder ℓ h hnm hT (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹)
    (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec f

/-- Recover the actual scaled pointwise jet from the measured weighted
norm at each active time, with the amplitude factor restored. -/
theorem norm_mixedWord_le_amplitudeSeminorm (holder : Prop) (ℓ h : ℝ) {n : ℕ} (hT : 0 < T)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (f : HierarchyTwistedProfile T k E) {w : List (Fin 4)}
    (hw : w ∈ hierarchyAdmissibleWords (Fin 4) n) {t : ℝ} (ht : t ∈ Icc t₀ T)
    (x : Vec3 × ℝ) :
    ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t, z)) x‖ ≤
      γ t * amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos f := by
  let A := Icc t₀ T
  have hA : A ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  obtain ⟨B, hb⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos
  have hBound (w' : List (Fin 4)) (_ : w' ∈ hierarchyAdmissibleWords (Fin 4) n) :
      BddAbove (hierarchyJetValues holder (hierarchyMixedDirection ℓ h) w'
        (weightedSlices A (fun u => (γ u)⁻¹) f)) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w' f hA _ hb
  have hjets := norm_word_le_hierarchyFiniteWordNorm holder hBound hw ⟨t, ht⟩ x
  have hs : ContDiff ℝ ∞ (fun z : Vec3 × ℝ => f.val.val.val (t, z)) := by
    have hs₁ := weightedSlices_smooth hA (fun _ => 1) f ⟨t, ht⟩
    change ContDiff ℝ ∞ (fun z : Vec3 × ℝ => (1 : ℝ) • f.val.val.val (t, z)) at hs₁
    simpa only [one_smul] using hs₁
  change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w
    (fun z => (γ t)⁻¹ • f.val.val.val (t, z)) x‖ ≤
      amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos f at hjets
  rw [phaseOperatorWord_const_smul (D := hierarchyMixedDirection ℓ h)
    (fun _ => contDiff_const) hs, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos t ht))] at hjets
  have hraw := mul_le_mul_of_nonneg_left hjets (hpos t ht).le
  rwa [← mul_assoc, mul_inv_cancel₀ (hpos t ht).ne', one_mul] at hraw

/-- Every mixed jet vanishes at a positive activation time if the profile
is identically zero on the preceding part of the slab. -/
theorem mixedWord_eq_zero_at_activation (hT : 0 < T) (ℓ h : ℝ) (w : List (Fin 4))
    (f : HierarchyTwistedProfile T k E) {t₀ : ℝ} (ht₀ : 0 < t₀) (htT : t₀ ≤ T)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, f.val.val.val (t, x) = 0)
    (x : Vec3 × ℝ) :
    phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t₀, z)) x = 0 := by
  let g := hierarchyTwistedMixedWord hT ℓ h w f
  have hc : ContinuousOn (fun t => g.val.val.val (t, x)) (Icc 0 T) :=
    (HierarchySmoothProfile.smooth g.val.val).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ ht => ⟨ht, mem_univ _⟩)
  have hsub : Ico 0 t₀ ⊆ Icc 0 T := fun _ ht => ⟨ht.1, ht.2.le.trans htT⟩
  have hcl : t₀ ∈ closure (Ico 0 t₀) := by
    rw [closure_Ico ht₀.ne]
    exact ⟨ht₀.le, le_rfl⟩
  have hg₀ (t : ℝ) (ht : t ∈ Ico 0 t₀) : g.val.val.val (t, x) = 0 := by
    change (hierarchyTwistedMixedWord hT ℓ h w f).val.val.val (t, x) = 0
    rw [hierarchyTwistedMixedWord_apply hT ℓ h w f (hsub ht),
      show (fun z => f.val.val.val (t, z)) = 0 from funext (hzero t (hsub ht) ht.2),
      actualWord_zero]
    rfl
  rw [← hierarchyTwistedMixedWord_apply hT ℓ h w f ⟨ht₀.le, htT⟩]
  exact ((hc t₀ ⟨ht₀.le, htT⟩).mono hsub).eq_const_of_mem_closure hcl hg₀

/-- The within-slab time derivative of a mixed jet also vanishes at
activation. Its derivative on the closed inactive prefix determines it. -/
theorem hasDerivWithinAt_mixedWord_zero_at_activation (hT : 0 < T) (ℓ h : ℝ) (w : List (Fin 4))
    (f : HierarchyTwistedProfile T k E) {t₀ : ℝ} (ht₀ : 0 < t₀) (htT : t₀ ≤ T)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, f.val.val.val (t, x) = 0)
    (x : Vec3 × ℝ) :
    HasDerivWithinAt (fun t => phaseOperatorWord (hierarchyMixedDirection ℓ h) w
      (fun z => f.val.val.val (t, z)) x) 0 (Icc 0 T) t₀ := by
  let g := hierarchyTwistedMixedWord hT ℓ h w f
  let G (t : ℝ) := g.val.val.val (t, x)
  have h₀ : t₀ ∈ Icc 0 T := ⟨ht₀.le, htT⟩
  have h₀' : t₀ ∈ Icc 0 t₀ := ⟨ht₀.le, le_rfl⟩
  have hsub : Icc 0 t₀ ⊆ Icc 0 T := Icc_subset_Icc_right htT
  have hG (t : ℝ) (ht : t ∈ Icc 0 T) : G t =
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun z => f.val.val.val (t, z)) x :=
    hierarchyTwistedMixedWord_apply hT ℓ h w f ht x
  have hs : ContDiffOn ℝ ∞ G (Icc 0 T) := (HierarchySmoothProfile.smooth g.val.val).comp
    (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ ht => ⟨ht, mem_univ _⟩)
  have hd := ((hs.differentiableOn (by simp)) t₀ h₀).hasDerivWithinAt
  have hz (t : ℝ) (ht : t ∈ Icc 0 t₀) : G t = 0 := by
    rw [hG t (hsub ht)]
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · rw [show (fun z => f.val.val.val (t, z)) = 0 from funext (hzero t (hsub ht) hlt),
        actualWord_zero]
      rfl
    · exact mixedWord_eq_zero_at_activation hT ℓ h w f ht₀ htT hzero x
  have hdz : HasDerivWithinAt G 0 (Icc 0 t₀) t₀ :=
    (hasDerivAt_const t₀ (0 : E)).hasDerivWithinAt.congr_of_mem hz h₀'
  have hu := uniqueDiffOn_Icc ht₀ t₀ h₀'
  have hd₀ := ((hd.mono hsub).derivWithin hu).symm.trans (hdz.derivWithin hu)
  exact (hd.congr_deriv hd₀).congr_of_mem (fun t ht => (hG t ht).symm) h₀

/-- A profile zero before activation has its full-slab unweighted seminorm
bounded by its weighted active seminorm when the amplitude is at most one. -/
theorem unweightedSeminorm_le_amplitudeSeminorm_of_inactive (holder : Prop) (ℓ h : ℝ) (n : ℕ)
    (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1) (f : HierarchyTwistedProfile T k E)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, f.val.val.val (t, x) = 0) :
    unweightedSeminorm holder ℓ h n hT f ≤ amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos f := by
  let A := Icc t₀ T
  let S := Icc (0 : ℝ) T
  let D := hierarchyMixedDirection ℓ h
  let u := weightedSlices S (fun _ => 1) f
  let v := weightedSlices A (fun t => (γ t)⁻¹) f
  have hA : A ⊆ S := Icc_subset_Icc_left ht₀
  obtain ⟨B, hb⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos
  change hierarchyFiniteWordNorm holder D n u ≤ hierarchyFiniteWordNorm holder D n v
  unfold hierarchyFiniteWordNorm
  refine Finset.sum_le_sum fun w _ => ?_
  have hv : BddAbove (hierarchyJetValues holder D w v) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w f hA _ hb
  have hV : 0 ≤ sSup (hierarchyJetValues holder D w v) := le_csSup hv (Or.inl rfl)
  have hu (t : S) : u t = fun x => f.val.val.val (t, x) := by
    funext x
    exact one_smul ℝ _
  have hvscale (t : S) (ht : (t : ℝ) ∈ A) (x : Vec3 × ℝ) :
      phaseOperatorWord D w (v ⟨t, ht⟩) x = (γ t)⁻¹ • phaseOperatorWord D w (u t) x := by
    have heq : v ⟨t, ht⟩ = fun x => (γ t)⁻¹ • u t x := by rw [hu]; rfl
    rw [heq]
    exact phaseOperatorWord_const_smul (D := D) (fun _ => contDiff_const)
      (weightedSlices_smooth (Subset.rfl : S ⊆ S) (fun _ => 1) f t) _ w x
  have hnorm (t : S) (ht : (t : ℝ) ∈ A) (z : E) : ‖z‖ ≤ ‖(γ t)⁻¹ • z‖ := by
    have hi : (1 : ℝ) ≤ (γ t)⁻¹ := by simpa using inv_anti₀ (hpos t ht) (hγle t ht)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos t ht))]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (norm_nonneg z)
  have hzeroWord (t : S) (ht : (t : ℝ) < t₀) : phaseOperatorWord D w (u t) = 0 := by
    rw [hu, show (fun x => f.val.val.val (t, x)) = 0 from funext (hzero t t.property ht),
      actualWord_zero]
  refine csSup_le (s := hierarchyJetValues holder D w u) ⟨0, Or.inl rfl⟩ ?_
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, t, x, y, rfl⟩)
  · exact hV
  · by_cases ht : (t : ℝ) < t₀
    · simpa only [hzeroWord t ht, Pi.zero_apply, norm_zero] using hV
    · have hta : (t : ℝ) ∈ A := ⟨le_of_not_gt ht, t.property.2⟩
      refine (hnorm t hta _).trans ?_
      rw [← hvscale t hta x]
      exact le_csSup hv (Or.inr (Or.inl ⟨⟨t, hta⟩, x, rfl⟩))
  · by_cases ht : (t : ℝ) < t₀
    · simpa only [hzeroWord t ht, Pi.zero_apply, sub_self, norm_zero, zero_div] using hV
    · have hta : (t : ℝ) ∈ A := ⟨le_of_not_gt ht, t.property.2⟩
      refine (div_le_div_of_nonneg_right (hnorm t hta _) (Real.sqrt_nonneg _)).trans ?_
      rw [smul_sub, ← hvscale t hta x, ← hvscale t hta y]
      exact le_csSup hv (Or.inr (Or.inr ⟨hH, ⟨t, hta⟩, x, y, rfl⟩))

/-- A whole-slab product with an inactive oscillatory factor is controlled
by the active weighted norm of that factor and the full norm of the other. -/
theorem unweightedSeminorm_bilinear_le_amplitude_of_inactive
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G)
    (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1) (f : HierarchyTwistedProfile T k E)
    (g : HierarchyTwistedProfile T k F) (fg : HierarchyTwistedProfile T k G)
    (heq : ∀ t ∈ Icc 0 T, ∀ x : Vec3 × ℝ,
      fg.val.val.val (t, x) = B (f.val.val.val (t, x)) (g.val.val.val (t, x)))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, g.val.val.val (t, x) = 0) :
    unweightedSeminorm holder ℓ h n hT fg ≤
      (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n *
        (2 * ‖B‖ * unweightedSeminorm holder ℓ h n hT f *
          amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos g) := by
  let D := hierarchyMixedDirection ℓ h
  let S := Icc (0 : ℝ) T
  let u : S → Vec3 × ℝ → E := weightedSlices S (fun _ => 1) f
  let v : S → Vec3 × ℝ → F := weightedSlices S (fun _ => 1) g
  have hS : S ⊆ Icc 0 T := Subset.rfl
  have h₁ : ∀ t ∈ S, ‖(1 : ℝ)‖ ≤ 1 := by simp
  have hfg : weightedSlices S (fun _ => 1) fg = fun t x => B (u t x) (v t x) := by
    funext t x
    change (1 : ℝ) • fg.val.val.val (t, x) =
      B ((1 : ℝ) • f.val.val.val (t, x)) ((1 : ℝ) • g.val.val.val (t, x))
    simpa only [one_smul] using heq t t.property x
  have hprod := hierarchyFiniteWordNorm_bilinear_le B holder (D := D) (fun _ => contDiff_const) n
    (f := u) (g := v) (weightedSlices_smooth hS _ f) (weightedSlices_smooth hS _ g)
    (fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w f hS _ h₁)
    (fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w g hS _ h₁)
  rw [← hfg] at hprod
  refine hprod.trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (unweightedSeminorm_le_amplitudeSeminorm_of_inactive holder ℓ h n hT ht₀ htT γ hγ hpos hγle g hzero)
      (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg B))
        (apply_nonneg (unweightedSeminorm holder ℓ h n hT) f))) (by positivity)

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- Measure the hierarchy and its forcing profiles using the actual spatial
supremum seminorm on the slab and the amplitude-weighted seminorm on the active interval. -/
noncomputable def actualMeasuredLevels (A : HierarchyOperators VP SP) (u : HierarchyProfiles VP SP)
    (P : ℕ) (completionSwitch parentResidual : VP) (freq : ℝ) (hf : 0 ≤ freq)
    (ℓ h : ℝ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t) :
    HierarchyMeasuredLevels :=
  let U : ℕ → Seminorm ℝ VP := fun n => unweightedSeminorm False ℓ h n hT
  let W : ℕ → Seminorm ℝ VP := fun n => amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
  let Q : ℕ → Seminorm ℝ SP := fun n => amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
  HierarchyMeasuredLevels.ofProfiles A u P completionSwitch parentResidual freq hf
    (fun n => U n) (fun n => W n) (fun n => Q n)
    (fun n => apply_nonneg (U n)) (fun n => apply_nonneg (W n)) (fun n => apply_nonneg (Q n))

/-- The reconstruction rows of the norm recurrence follow directly from
the actual seminorm and the formula `Yₚ = Vₚ + Cₚ₋₁`. -/
theorem actualMeasuredLevels_reconstruction (A : HierarchyOperators VP SP) (u : HierarchyProfiles VP SP)
    (P : ℕ) (completionSwitch parentResidual : VP) (freq : ℝ) (hf : 0 ≤ freq)
    (ℓ h : ℝ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t) (n p : ℕ) :
    let s := actualMeasuredLevels A u P completionSwitch parentResidual freq hf ℓ h hT ht₀ htT γ hγ hpos
    s.Y n p ≤ s.osc n p + s.completion n (p - 1) ∧ s.Z n p = s.Y n p + s.mean n p := by
  let W : Seminorm ℝ VP := amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
  let Q : Seminorm ℝ SP := amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
  refine ⟨?_, rfl⟩
  change W (u.V p + u.C (p - 1)) ≤ W (u.V p) + freq * Q (u.p p) + W (u.C (p - 1))
  exact (map_add_le_add W _ _).trans
    (add_le_add (le_add_of_nonneg_right (mul_nonneg hf (apply_nonneg Q _))) le_rfl)

end HierarchyTwistedProfile

end TorusEuler
