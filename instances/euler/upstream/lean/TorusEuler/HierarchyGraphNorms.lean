import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyPhysicalGraph
import TorusEuler.PhysicalHierarchyProfileBounds

/-! The measured finite profile norms on the actual Eulerian graph. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "Profile" => HierarchyTwistedProfile T k E

/-- The field in one actual time slice, still in label and phase variables. -/
def slice (f : Profile) (t : ℝ) (a : Vec3) (s : ℝ) : E :=
  f.val.val.val (t,a,s)

theorem contDiff_slice (f : Profile) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (Function.uncurry (slice f t)) := by
  simpa only [weightedSlices, LinearMap.coe_mk, AddHom.coe_mk, one_smul, slice, Function.uncurry_def]
    using weightedSlices_smooth (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T) (fun _ => 1) f ⟨t,ht⟩

/-- The true unweighted hierarchy seminorm supplies the scaled Fréchet jets
uniformly on the whole time slab. -/
theorem scaledPhaseProfile_jetBound_unweighted (hT : 0 < T) (ℓ h : ℝ) (n : ℕ)
    (f : Profile) {t : ℝ} (ht : t ∈ Icc 0 T) :
    PhaseJetBound n ((4 : ℝ) ^ n * unweightedSeminorm False ℓ h n hT f)
      (scaledPhaseProfile ℓ h (slice f t)) := by
  let I := Icc (0 : ℝ) T
  have hBound (w : List (Fin 4)) (_hw : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (weightedSlices I (fun _ => 1) f)) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w f (Subset.rfl : I ⊆ I)
      (fun _ => 1) (B := 1) (by simp)
  have hRelay := hierarchyRelayWordBound_of_finiteNorm hBound
  have hSlice : (weightedSlices I (fun _ => 1) f) =
      (fun (r : I) => Function.uncurry (slice f (r : ℝ))) := by
    ext r x
    exact one_smul ℝ _
  have hW : HierarchyRelayWordBound ℓ h n (unweightedSeminorm False ℓ h n hT f)
      (fun (r : I) => Function.uncurry (slice f (r : ℝ))) := by
    rw [← hSlice]
    exact hRelay
  exact scaledPhaseProfile_jetBound_of_hierarchyRelayWordBound hW (⟨t,ht⟩ : I)
    (contDiff_slice f ht)

/-- The actual weighted norm restores the seed amplitude on every active
slice before the change to Eulerian coordinates. -/
theorem scaledPhaseProfile_jetBound_weighted (hT : 0 < T) (ℓ h : ℝ) (n : ℕ)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ r ∈ Icc t₀ T, 0 < γ r)
    (f : Profile) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    PhaseJetBound n (γ t * ((4 : ℝ) ^ n * amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hγpos f))
      (scaledPhaseProfile ℓ h (slice f t)) := by
  let I := Icc t₀ T
  obtain ⟨B, hB⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hγpos
  have hBound (w : List (Fin 4)) (_hw : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (fun r : I => (γ r)⁻¹ • Function.uncurry (slice f (r : ℝ)))) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w f (Icc_subset_Icc_left ht₀)
      (fun r => (γ r)⁻¹) hB
  exact scaledPhaseProfile_jetBound_of_actual_weightedWordNorm hBound (⟨t,ht⟩ : I) (hγpos t ht)
    (contDiff_slice f ⟨ht₀.trans ht.1,ht.2⟩)

/-- A phase-independent field uses the same scaled jets with the phase scale
set to one. Its label value at phase zero determines the entire profile. -/
theorem scaledPhaseProfile_jetBound_of_mean (hT : 0 < T) (ℓ h : ℝ) (n : ℕ)
    (f : Profile) (hf : HierarchyPeriodicProfile.PhaseIndependent f.val.val)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    PhaseJetBound n ((4 : ℝ) ^ n * unweightedSeminorm False ℓ h n hT f)
      (scaledPhaseProfile ℓ 1 (fun a _ => slice f t a 0)) := by
  have hs := scaledPhaseProfile_jetBound_unweighted hT ℓ h n f ht
  have heq : scaledPhaseProfile ℓ h (slice f t) = scaledPhaseProfile ℓ 1 (fun a _ => slice f t a 0) := by
    funext x
    exact (hf (t,ℓ • x.1,0) ⟨ht,mem_univ _⟩ (h * x.2))
  rwa [heq] at hs

set_option maxHeartbeats 1500000 in
/-- Quantitative Eulerian graph evaluation of the actual weighted profile. -/
theorem graphRead_frequency_jetBound_weighted (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ r ∈ Icc t₀ T, 0 < γ r)
    (f : Profile) {A : Velocity} {t ℓ h D freq L C α : ℝ} {n a p : ℕ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc t₀ T) (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (hCarrier : ‖k‖ ≤ D * freq) (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ n, ∀ x, ℓ ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D)
    (hNorm : amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hγpos f ≤ C * D ^ p * freq ^ α) :
    PhaseJetBound n
      (((3 : ℝ) * (2 : ℝ) ^ n * (2 * L)) ^ n * ((4 : ℝ) ^ n * C) *
        D ^ ((max a 1 + 1) * n + p) * (γ t * freq ^ ((3 : ℝ) * n / 2 + α))) (graphRead A f t) := by
  have hs := scaledPhaseProfile_jetBound_weighted hT ℓ h n ht₀ htT γ hγ hγpos f ht
  have hjet : PhaseJetBound n (γ t * (((4 : ℝ) ^ n * C) * D ^ p * freq ^ α))
      (scaledPhaseProfile ℓ h (slice f t)) := by
    intro j hj x
    refine (hs j hj x).trans ?_
    calc
      _ ≤ γ t * ((4 : ℝ) ^ n * (C * D ^ p * freq ^ α)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNorm (by positivity)) (hγpos t ht).le
      _ = _ := by ring
  have hC' : 0 ≤ ((4 : ℝ) ^ n * C) := by positivity
  change PhaseJetBound n _ (transportedProfile A k (slice f) t)
  exact transportedHierarchyProfile_frequency_jetBound (A := A) (k := k) (f := slice f)
    (C := ((4 : ℝ) ^ n * C)) (gamma := γ t) (alpha := α) (p := p) (n := n) (a := a)
    hℓ hh hD hf hL hC' (hγpos t ht).le hLabel hWidth hCarrier hA hB hBreg
    (contDiff_slice f ⟨ht₀.trans ht.1,ht.2⟩) hcoeff hjet


end

end TorusEuler.HierarchyTwistedProfile
