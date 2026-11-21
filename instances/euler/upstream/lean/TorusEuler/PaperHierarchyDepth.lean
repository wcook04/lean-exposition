import TorusEuler.HierarchyFiniteOrderBudget
import TorusEuler.HierarchyPhysicalVelocityBounds

/-! The retained estimates and all-order remainder of Theorem 5.6. -/

open Set

namespace TorusEuler

/-- A retained quadratic interaction is independent of the final depth. -/
theorem hierarchyLevelPairs_eq_of_retained {P Q p shift : ℕ}
    (hp : p ≤ Q) (hQP : Q ≤ P) (hshift : shift ≤ 1) :
    hierarchyLevelPairs P shift p = hierarchyLevelPairs Q shift p := by
  apply Finset.ext
  intro ij
  constructor
  · intro h
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp h
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hm
    obtain ⟨hi₁, _⟩ := Finset.mem_Icc.mp hi
    obtain ⟨hj₁, _⟩ := Finset.mem_Icc.mp hj
    change ij.1 + ij.2 - shift = p at he
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, he⟩
    · exact Finset.mem_Icc.mpr ⟨hi₁, by omega⟩
    · exact Finset.mem_Icc.mpr ⟨hj₁, by omega⟩
  · intro h
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp h
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hm
    obtain ⟨hi₁, hi₂⟩ := Finset.mem_Icc.mp hi
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hi₁, by omega⟩,
        Finset.mem_Icc.mpr ⟨hj₁, by omega⟩⟩, he⟩

/-- Restrict the exact measured recurrence to a retained prefix. This allows a
level estimate to use constants and a derivative reserve depending on that level. -/
theorem HierarchyNormRecurrence.restrictDepth
    {s : HierarchyMeasuredLevels} {freq L K : ℝ} {P Q H : ℕ}
    (r : HierarchyNormRecurrence s freq L K P H) (hQP : Q ≤ P) :
    HierarchyNormRecurrence s freq L K Q H := by
  have hRetain {j b : ℕ} (h : j ∈ Finset.Icc b Q) : j ∈ Finset.Icc b P :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp h).1, (Finset.mem_Icc.mp h).2.trans hQP⟩
  refine ⟨r.seed, r.seedZeros, ?_, fun n hn p hp => r.meanSolve n hn p (hRetain hp), ?_,
    fun n hn p hp => r.oscSolve n hn p (hRetain hp),
    fun n hn p hp => r.complete n hn p (hRetain hp),
    fun n hn p hp => r.Ybound n hn p (hRetain hp), fun n hn p hp => r.Zbound n hn p (hRetain hp)⟩
  · intro n hn p hp
    have he := hierarchyLevelPairs_eq_of_retained (shift := 0) (Finset.mem_Icc.mp hp).2 hQP (by decide)
    rw [← he]
    exact r.meanForcing n hn p (hRetain hp)
  · intro n hn p hp
    have he₀ := hierarchyLevelPairs_eq_of_retained (shift := 0) (Finset.mem_Icc.mp hp).2 hQP (by decide)
    have he₁ := hierarchyLevelPairs_eq_of_retained (shift := 1) (Finset.mem_Icc.mp hp).2 hQP (by decide)
    rw [← he₀, ← he₁]
    exact r.oscForcing n hn p (hRetain hp)

private theorem hierarchy_loss_le_six {L : ℝ} (hL : 1 ≤ L) {r : ℕ} (hr : r ≤ 6) :
    L ^ r ≤ L ^ (6 : ℕ) := pow_le_pow_right₀ hL hr

/-- The three inequalities of Theorem 5.6 at each level, in the actual
measured rows when the supplied recurrence is the one for the physical profiles. -/
theorem HierarchyNormRecurrence.paper_level_bounds
    {s : HierarchyMeasuredLevels} {freq L K : ℝ} {P H n i : ℕ}
    (r : HierarchyNormRecurrence s freq L K P H)
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 1 ≤ K) (hs : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hi : i ∈ Finset.Icc 1 P) (hn : n + 3 * i ≤ H) :
    let A := 2 * hierarchyLevelConstant i K i
    s.osc n i + s.oscSource n i ≤ A * L ^ 6 * freq ^ hierarchyOscExponent i ∧
    s.mean n i + s.meanSource n i ≤ A * L ^ 6 * freq ^ hierarchyMeanExponent i ∧
    s.completion n i ≤ A * L ^ 6 * freq ^ hierarchyCompletionExponent i := by
  intro A
  obtain ⟨hi₁, hiP⟩ := Finset.mem_Icc.mp hi
  have hb := hierarchy_level_bounds (r.restrictDepth hiP) hf hL hK hs i hi₁ le_rfl n (by omega)
  let C := hierarchyLevelConstant i K i
  have hC : 0 ≤ C := zero_le_one.trans (hierarchyLevelConstant_one_le (zero_le_one.trans hK) _)
  have hLoss {e x : ℝ} {q : ℕ} (hq : q ≤ 6) (hx : x ≤ C * L ^ q * freq ^ e) :
      x ≤ C * L ^ (6 : ℕ) * freq ^ e :=
    hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hierarchy_loss_le_six hL hq) hC)
      (Real.rpow_nonneg (zero_le_one.trans hf) e))
  have hOsc := hLoss (q := 1) (by decide) (by simpa only [pow_one] using hb.osc)
  have hSource := hLoss (q := 0) (by decide) (by simpa only [pow_zero, mul_one] using hb.oscSource)
  have hMeanSource := hLoss (q := 5) (by decide) hb.meanSource
  have hCompletion := hLoss (q := 2) (by decide) hb.completion
  change s.osc n i + s.oscSource n i ≤ _ ∧ s.mean n i + s.meanSource n i ≤ _ ∧ _
  refine ⟨(add_le_add hOsc hSource).trans_eq ?_, (add_le_add hb.meanStrong hMeanSource).trans_eq ?_,
    hCompletion.trans ?_⟩
  · dsimp only [A, C]
    ring
  · dsimp only [A, C]
    ring
  · dsimp only [A, C]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      (Real.rpow_nonneg (zero_le_one.trans hf) _)
    linarith only [hC]

/-- Uniform constant for the sums at retained depth. -/
noncomputable def paperHierarchySumCost (P : ℕ) (C : ℝ) : ℝ :=
  2 * ((Finset.Icc 1 P).card : ℝ) * C

/-- Uniform constant for the remainder after absorption of the parent loss. -/
noncomputable def paperHierarchyTailCost (P : ℕ) (K C : ℝ) : ℝ :=
  2 * K * (C + 1) ^ 2 *
    (1 + ((hierarchyTailPairs P 0).card : ℝ) + 2 * ((hierarchyTailPairs P 1).card : ℝ))

namespace HierarchyTwistedProfile.PhysicalApproximationData

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- The exact averaged forcing of a retained mean correction, including the
transported parent residual in the first mean equation. -/
noncomputable def paperMeanSource (b : PhysicalApproximationData d p P) (i : ℕ) : VP :=
  -b.operators.average (b.operators.sourceBeforeMean b.profiles P b.leading.completionSwitch i) -
    (if i = 2 then b.parentResidual else 0)

/-- The measured bounds on the retained levels give the exact two sums
in (5.45), including the sum of the mean sources. -/
theorem paper_hierarchy_sums
    (b : PhysicalApproximationData d p P) (hP : 1 ≤ P) (n : ℕ)
    {ℓ h freq L C : ℝ} (hf : 1 ≤ freq) (hL : 1 ≤ L) (hC : 0 ≤ C)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hLevels : ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ℓ h hT ht₀ htT γ hγ hpos) freq L C n i) :
    let F := b.profiles.velocity P
    let N := unweightedSeminorm False ℓ h n hT
    let W := amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
    W (F - b.operators.average F) ≤ paperHierarchySumCost P C * L ^ 6 * freq ^ (-5 / 4 : ℝ) ∧
    N (∑ i ∈ Finset.Icc 2 P, b.profiles.B i) + N (∑ i ∈ Finset.Icc 2 P, b.paperMeanSource i) ≤
      paperHierarchySumCost P C * L ^ 6 * freq ^ (-5 / 2 : ℝ) := by
  intro F N W
  let kP : ℝ := (Finset.Icc 1 P).card
  have hkP : 0 ≤ kP := Nat.cast_nonneg _
  have hFreq : 0 ≤ freq := zero_le_one.trans hf
  have hPow0 : 0 ≤ freq ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hFreq _
  have hFreqBound (i : ℕ) (hi : 2 ≤ i) :
      freq ^ hierarchyMeanExponent i ≤ freq ^ (-5 / 2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hf
    unfold hierarchyMeanExponent
    have hi' : (2 : ℝ) ≤ i := by exact_mod_cast hi
    linarith
  have hB i (hi : i ∈ Finset.Icc 2 P) :
      N (b.profiles.B i) ≤ C * L ^ (6 : ℕ) * freq ^ (-5 / 2 : ℝ) := by
    have hx := hLevels i (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hi).1; omega,
      (Finset.mem_Icc.mp hi).2⟩)
    exact hx.meanStrong.trans (mul_le_mul_of_nonneg_left (hFreqBound i (Finset.mem_Icc.mp hi).1)
      (by positivity))
  have hSource i (hi : i ∈ Finset.Icc 2 P) :
      N (b.paperMeanSource i) ≤ C * L ^ (6 : ℕ) * freq ^ (-5 / 2 : ℝ) := by
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hi
    have hx := hLevels i (Finset.mem_Icc.mpr ⟨by omega, hhi⟩)
    have hs : N (b.paperMeanSource i) ≤ C * L ^ (5 : ℕ) * freq ^ hierarchyMeanExponent i := by
      simpa only [actualMeasuredLevels, HierarchyMeasuredLevels.ofProfiles, ite_eq_right (show i ≠ 1 by omega),
        paperMeanSource] using hx.meanSource
    exact hs.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hierarchy_loss_le_six hL (by decide)) hC)
      (hFreqBound i hlo) (Real.rpow_nonneg hFreq _) (by positivity))
  have hsum (u : ℕ → VP) (hu : ∀ i ∈ Finset.Icc 2 P, N (u i) ≤ C * L ^ 6 * freq ^ (-5 / 2 : ℝ)) :
      N (∑ i ∈ Finset.Icc 2 P, u i) ≤ kP * (C * L ^ 6 * freq ^ (-5 / 2 : ℝ)) := by
    have hTriangle : N (∑ i ∈ Finset.Icc 2 P, u i) ≤ ∑ i ∈ Finset.Icc 2 P, N (u i) := by
      let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
      exact norm_sum_le (Finset.Icc 2 P) u
    refine hTriangle.trans ?_
    calc
      _ ≤ ∑ _i ∈ Finset.Icc 2 P, (C * L ^ 6 * freq ^ (-5 / 2 : ℝ)) := Finset.sum_le_sum hu
      _ = ((Finset.Icc 2 P).card : ℝ) * (C * L ^ 6 * freq ^ (-5 / 2 : ℝ)) := by simp
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        change ((Finset.Icc 2 P).card : ℝ) ≤ ((Finset.Icc 1 P).card : ℝ)
        exact_mod_cast Finset.card_le_card (Finset.Icc_subset_Icc_left (by decide : 1 ≤ (2 : ℕ)))
  have hW := (b.velocityProfileSums_of_actualLevels hP n hf hL hC ht₀ htT γ hγ hpos hLevels).1
  refine ⟨hW.trans ?_, (add_le_add (hsum _ hB) (hsum _ hSource)).trans_eq ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (hierarchy_loss_le_six hL (by decide)) (by positivity)) (Real.rpow_nonneg hFreq _)
  · unfold paperHierarchySumCost
    dsimp only [kP]
    ring

end HierarchyTwistedProfile.PhysicalApproximationData

end TorusEuler
