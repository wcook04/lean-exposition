import TorusEuler.HierarchyConcreteRecurrence
import TorusEuler.HierarchySlowInteractionEstimates

/-! The exact physical source terms in the weighted hierarchy recurrence. -/

open Set

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "Q²(" n ")" => hierarchyQuadraticConstant (Fin 4) n ^ (2 : ℕ)

set_option maxHeartbeats 3000000 in
/-- The actual slow and fast source estimates populate the ordered
recurrence with the common budget. The linear relay and parent residual
have their own bounds, and the exact averaged and centered identities
are kept as equations of the selected sources. -/
theorem actualMeasuredLevels_sourceTermBounds (hT : 0 < T) (G M : MP) (κ : VP)
    (u : HierarchyProfiles VP SP) (P H : ℕ) (completionSwitch residual : VP)
    {freq L K : ℝ} (hf : 0 ≤ freq) (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (hh : h ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hGphase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hVzero : ∀ p, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.V p).val.val.val (t,x) = 0)
    (hCzero : ∀ p, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.C p).val.val.val (t,x) = 0)
    (rowCap : ℕ → ℝ)
    (hrow : ∀ n, n + 1 ≤ H → ∀ i : Fin 3,
      unweightedSeminorm False ℓ h n hT (scaledCoframeRowProfile ℓ G i) ≤ rowCap n)
    (hRowCap : ∀ n, n + 1 ≤ H → 2 * (3 * Q²(n) * rowCap n) ≤ K * L)
    (hFastCap : ∀ n, n + 1 ≤ H →
      (2 * Q²(n)) * unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) ≤
        K * L * freq ^ (3 / 2 : ℝ)) :
    let A := twistedHierarchyOperators hT G M κ
    let U : ℕ → Seminorm ℝ VP := fun n => unweightedSeminorm False ℓ h n hT
    let W : ℕ → Seminorm ℝ VP := fun n => amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hγpos
    let s := actualMeasuredLevels A u P completionSwitch residual freq hf ℓ h hT ht₀ htT γ hγ hγpos
    let divProduct := fun i j => slowLabelDivergenceProduct hT G (u.V i) (u.Y j)
    (∀ i, A.average (u.B i) = u.B i) →
    (∀ p ∈ Finset.Icc 2 P, A.average (A.sourceBeforeMean u P completionSwitch p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2)) + A.average (divProduct ij.1 ij.2) +
          A.labelAdv (u.B ij.1) (u.B ij.2))) →
    (∀ p ∈ Finset.Icc 2 P, A.average (A.relayAtLevel u completionSwitch p) = 0) →
    (∀ n, n + 1 ≤ H → U n residual ≤ K * freq ^ hierarchyMeanExponent 2) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P,
      W n (A.relayAtLevel u completionSwitch p) ≤ K * L *
        (freq ^ (-1 : ℝ) * (s.osc (n+1) (p-1) + s.oscSource (n+1) (p-1)))) →
    HierarchySourceTermBounds A u completionSwitch residual divProduct U W s freq L K P H := by
  intro A U W s divProduct hB hExact hCentered hResidual hRelay
  have hYzero (i : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (hl : t < t₀) (x : Vec3 × ℝ) :
      (u.Y i).val.val.val (t,x) = 0 := by
    change (u.V i).val.val.val (t,x) + (u.C (i-1)).val.val.val (t,x) = 0
    rw [hVzero i t ht hl x, hCzero (i-1) t ht hl x, add_zero]
  have hSlow (n : ℕ) (hn : n + 1 ≤ H) : 3 * Q²(n) * rowCap n ≤ K * L := by
    have hcap := hRowCap n hn
    have hn' := (apply_nonneg (unweightedSeminorm False ℓ h n hT) (scaledCoframeRowProfile ℓ G 0)).trans
      (hrow n hn 0)
    exact (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans hcap
  have hMeanTerms (n : ℕ) (hn : n+1 ≤ H) (i j : ℕ) :=
    actualMeasuredLevels_meanForcing_slow_terms ht₀ htT γ hγ hγpos hT G M κ ℓ h hℓ n (hrow n hn) u P
      completionSwitch residual freq hf i j hγle hYzero (hVzero i)
  have hYnonneg (n i : ℕ) : 0 ≤ s.Y n i := (s.nonneg n i).2.2.2.2.2.1
  have hZnonneg (n i : ℕ) : 0 ≤ s.Z n i := (s.nonneg n i).2.2.2.2.2.2
  have hOscNonneg (n i : ℕ) : 0 ≤ s.osc n i := (s.nonneg n i).2.2.1
  have hMeanNonneg (n i : ℕ) : 0 ≤ s.mean n i := (s.nonneg n i).2.2.2.1
  have hCompletionNonneg (n i : ℕ) : 0 ≤ s.completion n i := (s.nonneg n i).2.2.2.2.1
  refine ⟨hExact,hCentered,?_,?_,?_,hResidual,hRelay,?_,?_,?_⟩
  · intro n hn p hp ij hij
    exact (hMeanTerms n hn ij.1 ij.2).1.trans
      (mul_le_mul_of_nonneg_right (hSlow n hn) (mul_nonneg (hYnonneg _ _) (hYnonneg _ _)))
  · intro n hn p hp ij hij
    exact (hMeanTerms n hn ij.1 ij.2).2.1.trans
      (mul_le_mul_of_nonneg_right (hSlow n hn) (mul_nonneg (hOscNonneg _ _) (hYnonneg _ _)))
  · intro n hn p hp ij hij
    exact (hMeanTerms n hn ij.1 ij.2).2.2.trans
      (mul_le_mul_of_nonneg_right (hSlow n hn) (mul_nonneg (hMeanNonneg _ _) (hMeanNonneg _ _)))
  · rintro n hn p hp ⟨i,j⟩ hij
    have hs := amplitudeSeminorm_centered_labelProduct_le_succ ht₀ htT γ hγ hγpos hT G M κ ℓ h hℓ
      n (hrow n hn) u i j hγle (hYzero j)
      (average_labelAdv_independent_independent hT G M κ _ _ hGphase (hB i) (hB j))
    change W n (A.labelProduct u (i,j) - A.average (A.labelProduct u (i,j))) ≤ _ at hs
    exact hs.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hRowCap n hn)
      (hZnonneg (n+1) i)) (hZnonneg (n+1) j)).trans_eq (by ring))
  · rintro n hn p hp ⟨i,j⟩ hij
    have hs := amplitudeSeminorm_centered_phaseAdv_le_of_inactive ℓ h hh n hT G M κ (u.C (i-1))
      (u.Y j) ht₀ htT γ hγ hγpos hγle (hCzero (i-1))
    refine hs.trans ?_
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hFastCap n hn)
      (hCompletionNonneg n (i-1))) (hYnonneg (n+1) j)).trans_eq (by ring)
  · rintro n hn p hp ⟨i,j⟩ hij
    have hs := amplitudeSeminorm_phaseAdv_le ℓ h hh n hT G M κ (u.B i) (u.Y j) ht₀ htT γ hγ hγpos
    refine hs.trans ?_
    have hcost : Q²(n) * unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) ≤
        K * L * freq ^ (3 / 2 : ℝ) := by
      refine (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans ?_
      simpa only [mul_assoc] using hFastCap n hn
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost
      (hMeanNonneg n i)) (hYnonneg (n+1) j)).trans_eq (by ring)

end

end TorusEuler.HierarchyTwistedProfile
