import TorusEuler.TerminalHierarchyPhaseTime
import TorusEuler.TerminalTimeLeibniz
import TorusEuler.HierarchyTwistedFastSourceBounds

/-! Bounds for the linear profile operations used in the mixed-time hierarchy. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}
  {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- One of the three scaled label directions or the scaled independent phase direction. -/
abbrev scaledProfileDerivative (hT : 0 < T) (ell h : ℝ) (i : Fin 4) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k E :=
  directionDerivative hT (0, hierarchyMixedDirection ell h i 0)

theorem scaledProfileDerivative_apply (hT : 0 < T) (ell h : ℝ) (i : Fin 4)
    (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (scaledProfileDerivative hT ell h i f).val.val.val (t, x) =
      phaseDirectionalDerivative (hierarchyMixedDirection ell h i)
        (fun y => f.val.val.val (t, y)) x := by
  have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  rw [scaledProfileDerivative, directionDerivative_apply hT _ _ hx]
  have hf := ((HierarchySmoothProfile.smooth f.val.val).differentiableOn (by simp)
    (t, x) hx).hasFDerivWithinAt
  let I := ContinuousLinearMap.inr ℝ ℝ (Vec3 × ℝ)
  have hi : HasFDerivAt (fun y : Vec3 × ℝ => (t,y)) I x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hslice : fderiv ℝ (fun y => f.val.val.val (t,y)) x =
      (fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T) (t,x)).comp I :=
    (hf.comp_hasFDerivAt x hi (Filter.Eventually.of_forall fun _ => ⟨ht, mem_univ _⟩)).fderiv
  rw [phaseDirectionalDerivative, hslice]
  rfl

theorem timeJet_scaledProfileDerivative (hT : 0 < T) (j : ℕ) (ell h : ℝ) (i : Fin 4)
    (f : HierarchyTwistedProfile T k E) :
    timeJet hT j (scaledProfileDerivative hT ell h i f) =
      scaledProfileDerivative hT ell h i (timeJet hT j f) :=
  timeJet_directionDerivative hT j _ f

theorem boundedWeightSeminorm_scaledProfileDerivative_le (holder : Prop)
    (hT : 0 < T) (ell h : ℝ) (i : Fin 4) (n : ℕ) (f : HierarchyTwistedProfile T k E)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C) :
    boundedWeightSeminorm holder ell h n hT hA τ hτ (scaledProfileDerivative hT ell h i f) ≤
      boundedWeightSeminorm holder ell h (n + 1) hT hA τ hτ f := by
  let d (j : Fin 4) := hierarchyMixedDirection ell h j 0
  let W := weightedSlices A τ f
  have hB (w : List (Fin 4)) (_ : w ∈ hierarchyAdmissibleWords (Fin 4) (n + 1)) :
      BddAbove (hierarchyJetValues holder (fun j (_ : Vec3 × ℝ) => d j) w W) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ell h holder w f hA τ hτ
  have hb := (hierarchyFiniteWordNorm_constDerivative_le holder d
    (weightedSlices_smooth hA τ f) i n hB).2
  have heq : weightedSlices A τ (scaledProfileDerivative hT ell h i f) =
      fun t => phaseDirectionalDerivative (fun _ => d i) (W t) := by
    funext t x
    change τ t • (scaledProfileDerivative hT ell h i f).val.val.val (t, x) =
      fderiv ℝ (τ t • fun y => f.val.val.val (t, y)) x (d i)
    rw [scaledProfileDerivative_apply hT ell h i f (hA t.property), fderiv_const_smul_field]
    rfl
  simp only [boundedWeightSeminorm_apply, heq]
  exact hb

theorem timeJetSeminorm_scaledProfileDerivative_le (holder : Prop)
    (hT : 0 < T) (q : ℕ) (ell h : ℝ) (i : Fin 4) (n : ℕ) (f : HierarchyTwistedProfile T k E)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C) :
    timeJetSeminorm hT q (boundedWeightSeminorm holder ell h n hT hA τ hτ)
        (scaledProfileDerivative hT ell h i f) ≤
      timeJetSeminorm hT q (boundedWeightSeminorm holder ell h (n + 1) hT hA τ hτ) f := by
  simpa only [one_mul] using timeJetSeminorm_le_of_jetwise_le hT q _ _ f _ 1 (fun j _ => by
    rw [timeJet_scaledProfileDerivative, one_mul]
    exact boundedWeightSeminorm_scaledProfileDerivative_le holder hT ell h i n _ hA τ hτ)

/-- Spatial multiplication has its existing finite-order constant in the time norm. -/
def terminalHierarchyProductCost (B : E →L[ℝ] F →L[ℝ] G) (n : ℕ) : ℝ :=
  ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ) * (2 : ℝ) ^ n * (2 * ‖B‖)

theorem timeJetSeminorm_pointwiseBilinear_weighted_le (hT : 0 < T) (q : ℕ)
    (B : E →L[ℝ] F →L[ℝ] G) (holder : Prop) (ell h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C)
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F) :
    timeJetSeminorm hT q (boundedWeightSeminorm holder ell h n hT hA τ hτ)
        (pointwiseBilinear B f g) ≤ terminalHierarchyProductCost B n *
      (timeJetSeminorm hT q (unweightedSeminorm holder ell h n hT) f *
        timeJetSeminorm hT q (boundedWeightSeminorm holder ell h n hT hA τ hτ) g) := by
  apply timeJetSeminorm_pointwiseBilinear_le hT q B
  · unfold terminalHierarchyProductCost
    positivity
  · intro u v
    have hB := boundedWeightSeminorm_bilinear_le B holder ell h n hT hA
      (fun _ => 1) τ τ (Cf := 1) (fun _ _ => by simp) hτ hτ (fun _ _ => (one_mul _).symm)
      u v (pointwiseBilinear B u v)
      (fun t ht x => pointwiseBilinear_eval B u v ⟨hA ht, mem_univ _⟩)
    have hU := boundedWeightSeminorm_mono_time holder ell h n hT hA
      (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T) (fun _ => 1) (C := 1) (by simp) u
    let N : Seminorm ℝ (HierarchyTwistedProfile T k F) := boundedWeightSeminorm holder ell h n hT hA τ hτ
    let N₁ : Seminorm ℝ (HierarchyTwistedProfile T k E) := boundedWeightSeminorm holder ell h n hT hA (fun _ => 1) (B := 1) (by simp)
    let C₀ := terminalHierarchyProductCost B n
    have hC₀ : 0 ≤ C₀ := by unfold C₀ terminalHierarchyProductCost; positivity
    calc
      _ ≤ C₀ * (N₁ u * N v) := hB.trans_eq (by dsimp only [C₀, N₁, N, terminalHierarchyProductCost]; ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hU (apply_nonneg N v)) hC₀

theorem timeJetSeminorm_applyField_weighted_le (hT : 0 < T) (q : ℕ)
    (holder : Prop) (ell h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C)
    (B : HierarchyTwistedProfile T k (E →L[ℝ] F)) (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT q (boundedWeightSeminorm holder ell h n hT hA τ hτ) (applyField B f) ≤
      terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ F (E := E)).flip n *
      (timeJetSeminorm hT q (unweightedSeminorm holder ell h n hT) B *
        timeJetSeminorm hT q (boundedWeightSeminorm holder ell h n hT hA τ hτ) f) := by
  let L := (ContinuousLinearMap.apply ℝ F (E := E)).flip
  have he : applyField B f = pointwiseBilinear L B f := by
    apply HierarchyTwistedProfile.ext
    intro x hx
    rw [applyField_eval B f hx, pointwiseBilinear_eval L B f hx]
    rfl
  rw [he]
  exact timeJetSeminorm_pointwiseBilinear_weighted_le hT q L holder ell h n hA τ hτ B f

theorem timeJetSeminorm_le_amplitude_of_inactive (hT : 0 < T) (q : ℕ)
    (holder : Prop) (ell h : ℝ) (n : ℕ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hle : ∀ t ∈ Icc t₀ T, γ t ≤ 1) (f : HierarchyTwistedProfile T k E)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, f.val.val.val (t,x) = 0) :
    timeJetSeminorm hT q (unweightedSeminorm holder ell h n hT) f ≤
      timeJetSeminorm hT q (amplitudeSeminorm holder ell h n hT ht₀ htT γ hγ hpos) f := by
  simpa only [one_mul] using (timeJetSeminorm_le_of_jetwise_le hT q
    (amplitudeSeminorm holder ell h n hT ht₀ htT γ hγ hpos)
    (unweightedSeminorm holder ell h n hT) f f 1 fun j _ => by
      rw [one_mul]
      exact unweightedSeminorm_le_amplitudeSeminorm_of_inactive holder ell h n hT ht₀ htT
        γ hγ hpos hle (timeJet hT j f) fun _ ht ht' x => timeJet_zero_of_inactive hT f hzero j ht ht' x)

theorem timeJetSeminorm_phasePrimitiveProfile_le [CompleteSpace E] (hT : 0 < T)
    (q : ℕ) (f : HierarchyTwistedProfile T k E) (hf : PhaseMeanZero f)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C) (ell h : ℝ) (n : ℕ) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ)
        (phasePrimitiveProfile hT f hf) ≤
      2 * timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ) f := by
  apply timeJetSeminorm_le_of_jetwise_le
  intro j _
  rw [timeJet_phasePrimitiveProfile]
  exact boundedWeightSeminorm_phasePrimitiveProfile_le hT _ _ hA τ hτ ell h n

theorem timeJetSeminorm_average_le (hT : 0 < T) (q : ℕ)
    (ell h : ℝ) (n : ℕ)
    (G M : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)) (κ f : HierarchyTwistedProfile T k Vec3)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ)
        ((twistedHierarchyOperators hT G M κ).average f) ≤
      timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ) f := by
  let N : Seminorm ℝ (HierarchyTwistedProfile T k Vec3) := boundedWeightSeminorm False ell h n hT hA τ hτ
  simpa only [one_mul] using timeJetSeminorm_le_of_jetwise_le hT q N N f
    ((twistedHierarchyOperators hT G M κ).average f) 1 (fun j _ => by
      change N (timeJet hT j (profilePhaseAverage hT f)) ≤ _
      rw [timeJet_profilePhaseAverage, one_mul]
      exact boundedWeightSeminorm_average_le ell h n hT G M κ _ hA τ hτ)

end

end TorusEuler.HierarchyTwistedProfile
