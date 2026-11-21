import TorusEuler.HierarchyGraphNorms

/-! Whole-slab and phase-independent quantitative graph readout. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "Profile" => HierarchyTwistedProfile T k E

set_option maxHeartbeats 1100000 in
/-- The whole-slab depth remainder incurs the same frequency factor as the
weighted graph readout with unit amplitude. -/
theorem graphRead_frequency_jetBound_unweighted (hT : 0 < T) (f : Profile)
    {A : Velocity} {t ℓ h D freq L C α : ℝ} {n a p : ℕ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc 0 T) (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (hCarrier : ‖k‖ ≤ D * freq) (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ n, ∀ x, ℓ ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D)
    (hNorm : unweightedSeminorm False ℓ h n hT f ≤ C * D ^ p * freq ^ α) :
    PhaseJetBound n
      (((3 : ℝ) * (2 : ℝ) ^ n * (2 * L)) ^ n * ((4 : ℝ) ^ n * C) *
        D ^ ((max a 1 + 1) * n + p) * freq ^ ((3 : ℝ) * n / 2 + α)) (graphRead A f t) := by
  have hγ : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 T) := continuousOn_const
  have hpos : ∀ r ∈ Icc 0 T, (0 : ℝ) < 1 := fun _ _ => zero_lt_one
  have hBound : amplitudeSeminorm False ℓ h n hT le_rfl hT.le (fun _ => 1) hγ hpos f ≤
      C * D ^ p * freq ^ α := by
    simpa only [amplitudeSeminorm_apply, unweightedSeminorm, boundedWeightSeminorm_apply, inv_one] using hNorm
  have hj := graphRead_frequency_jetBound_weighted (a := a) (p := p) hT le_rfl hT.le (fun _ => 1) hγ hpos
    f ht hℓ hh hD hf hL hC hLabel hWidth hCarrier hA hB hBreg hcoeff hBound
  simpa only [one_mul] using hj

set_option maxHeartbeats 1100000 in
/-- The mean and its force only incur the label-derivative costs through
the same inverse parent graph. -/
theorem graphRead_frequency_jetBound_mean (hT : 0 < T) (f : Profile)
    (hmean : HierarchyPeriodicProfile.PhaseIndependent f.val.val)
    {A : Velocity} {t ℓ h D freq L C α : ℝ} {n a p : ℕ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc 0 T) (hℓ : 0 < ℓ) (hD : 1 ≤ D) (hf : 0 < freq)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hLabel : ℓ⁻¹ ≤ D ^ a) (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ n, ∀ x, ℓ ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D)
    (hNorm : unweightedSeminorm False ℓ h n hT f ≤ C * D ^ p * freq ^ α) :
    PhaseJetBound n
      (((3 : ℝ) * (2 : ℝ) ^ n * L) ^ n * ((4 : ℝ) ^ n * C) * D ^ ((a + 1) * n + p) * freq ^ α)
      (graphRead A f t) := by
  let mean (x : Vec3) := slice f t x 0
  have hm : ContDiff ℝ ∞ mean := (contDiff_slice f ht).comp (contDiff_id.prodMk contDiff_const)
  have hs := scaledPhaseProfile_jetBound_of_mean hT ℓ h n f hmean ht
  have hj : PhaseJetBound n (((4 : ℝ) ^ n * C) * D ^ p * freq ^ α)
      (scaledPhaseProfile ℓ 1 (fun x _ => mean x)) := by
    intro j hj x
    refine (hs j hj x).trans ?_
    calc
      _ ≤ (4 : ℝ) ^ n * (C * D ^ p * freq ^ α) := mul_le_mul_of_nonneg_left hNorm (by positivity)
      _ = _ := by ring
  have hGraph : graphRead A f t = mean ∘ A t := by
    funext x
    exact hmean (t,A t x,0) ⟨ht,mem_univ _⟩ _
  rw [hGraph]
  exact transportedHierarchyMean_frequency_jetBound (C := (4 : ℝ) ^ n * C) (a := a) (p := p)
    hℓ hD hf hL (by positivity) hLabel hA hB hBreg hm hcoeff hj

end

end TorusEuler.HierarchyTwistedProfile
