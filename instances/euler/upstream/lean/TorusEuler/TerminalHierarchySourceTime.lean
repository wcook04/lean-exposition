import TorusEuler.TerminalHierarchyNonlinearTime
import TorusEuler.TerminalHierarchyTime

/-! The actual retained and omitted hierarchy terms in the mixed-time recurrence. -/

open Set Finset

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "Q²(" n ")" => hierarchyQuadraticConstant (Fin 4) n ^ (2 : ℕ)

private theorem time_source_product_le {c d x a y b : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (hx : 0 ≤ x) (hxa : x ≤ a) (hy : 0 ≤ y) (hyb : y ≤ b) :
    c * x * y ≤ d * (a * b) := by
  rw [mul_assoc]
  exact mul_le_mul hcd (mul_le_mul hxa hyb hy (hx.trans hxa))
    (mul_nonneg hx hy) (hc.trans hcd)

private theorem timeJetSeminorm_unweighted_order_le (hT : 0 < T) (q : ℕ) (ℓ h : ℝ)
    {n m : ℕ} (hnm : n ≤ m) (f : VP) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) f ≤
      timeJetSeminorm hT q (unweightedSeminorm False ℓ h m hT) f :=
  timeJetSeminorm_mono_seminorm hT q
    (Seminorm.le_def.mpr (unweightedSeminorm_mono_order False ℓ h hnm hT)) f

set_option maxHeartbeats 2500000 in
/-- The mixed recurrence uses the original exact source identities, with
the retained mean force measured at time order q−1 and the oscillatory
force measured at time order q. -/
theorem actualMixedMeasuredLevels_sourceTermBounds (hT : 0 < T) (q : ℕ) (G M : MP) (κ : VP)
    (u : HierarchyProfiles VP SP) (P H : ℕ) (completionSwitch residual : VP)
    {freq L K : ℝ} (hf : 0 ≤ freq) (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (hh : h ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hGphase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hVzero : ∀ p, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.V p).val.val.val (t,x) = 0)
    (hCzero : ∀ p, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.C p).val.val.val (t,x) = 0)
    (rowCap : ℕ → ℝ)
    (hrow : ∀ n, n + 1 ≤ H → ∀ i : Fin 3, timeJetSeminorm hT q
      (unweightedSeminorm False ℓ h n hT) (scaledCoframeRowProfile ℓ G i) ≤ rowCap n)
    (hRowCap : ∀ n, n + 1 ≤ H → 2 * (3 * Q²(n) * rowCap n) ≤ K * L)
    (hFastCap : ∀ n, n + 1 ≤ H →
      (2 * Q²(n)) * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
        (scaledPhaseCoefficientProfile h κ) ≤ K * L * freq ^ (3 / 2 : ℝ)) :
    let A := twistedHierarchyOperators hT G M κ
    let U : ℕ → Seminorm ℝ VP := fun n => timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
    let Uf : ℕ → Seminorm ℝ VP := fun n => timeJetSeminorm hT (q - 1) (unweightedSeminorm False ℓ h n hT)
    let W : ℕ → Seminorm ℝ VP := fun n =>
      timeJetSeminorm hT q (amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hγpos)
    let Wp : ℕ → Seminorm ℝ SP := fun n =>
      timeJetSeminorm hT q (amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hγpos)
    let s := HierarchyMeasuredLevels.ofProfilesWithMeanForce A u P completionSwitch residual freq hf U Uf W Wp
    let divProduct := fun i j => slowLabelDivergenceProduct hT G (u.V i) (u.Y j)
    (∀ i, A.average (u.B i) = u.B i) →
    (∀ p ∈ Finset.Icc 2 P, A.average (A.sourceBeforeMean u P completionSwitch p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2)) + A.average (divProduct ij.1 ij.2) +
          A.labelAdv (u.B ij.1) (u.B ij.2))) →
    (∀ p ∈ Finset.Icc 2 P, A.average (A.relayAtLevel u completionSwitch p) = 0) →
    (∀ n, n + 1 ≤ H → Uf n residual ≤ K * L * freq ^ hierarchyMeanExponent 2) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P,
      W n (A.relayAtLevel u completionSwitch p) ≤ K * L *
        (freq ^ (-1 : ℝ) * (s.osc (n+1) (p-1) + s.oscSource (n+1) (p-1)))) →
    HierarchySourceTermBounds A u completionSwitch residual divProduct Uf W s freq L K P H (some L) := by
  intro A U Uf W Wp s divProduct hB hExact hCentered hResidual hRelay
  have hYzero (i : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (hl : t < t₀) (x : Vec3 × ℝ) :
      (u.Y i).val.val.val (t,x) = 0 := by
    change (u.V i).val.val.val (t,x) + (u.C (i-1)).val.val.val (t,x) = 0
    rw [hVzero i t ht hl x, hCzero (i-1) t ht hl x, add_zero]
  have hTime (n : ℕ) (f : VP) : Uf n f ≤ U n f :=
    timeJetSeminorm_mono hT (Nat.sub_le q 1) _ f
  have hSlow₀ (n : ℕ) (hn : n + 1 ≤ H) : 0 ≤ 3 * Q²(n) * rowCap n :=
    mul_nonneg (by positivity) ((apply_nonneg _ _).trans (hrow n hn 0))
  have hSlow (n : ℕ) (hn : n + 1 ≤ H) : 3 * Q²(n) * rowCap n ≤ K * L :=
    (le_mul_of_one_le_left (hSlow₀ n hn) (by norm_num)).trans (hRowCap n hn)
  have hrowForce (n : ℕ) (hn : n+1 ≤ H) (i : Fin 3) :
      timeJetSeminorm hT (q-1) (unweightedSeminorm False ℓ h n hT)
        (scaledCoframeRowProfile ℓ G i) ≤ rowCap n :=
    (timeJetSeminorm_mono hT (Nat.sub_le q 1) _ _).trans (hrow n hn i)
  have hYforce (n i : ℕ) : Uf n (u.Y i) ≤ W n (u.Y i) :=
    (hTime n _).trans (timeJetSeminorm_le_amplitude_of_inactive hT q False ℓ h n
      ht₀ htT γ hγ hγpos hγle _ (hYzero i))
  have hVforce (n i : ℕ) : Uf n (u.V i) ≤ s.osc n i := by
    refine ((hTime n _).trans (timeJetSeminorm_le_amplitude_of_inactive hT q False ℓ h n
      ht₀ htT γ hγ hγpos hγle _ (hVzero i))).trans ?_
    exact le_add_of_nonneg_right (mul_nonneg hf (apply_nonneg (Wp n) _))
  have hYForceHere (n i : ℕ) : Uf n (u.Y i) ≤ W (n+1) (u.Y i) :=
    (timeJetSeminorm_unweighted_order_le hT (q-1) ℓ h (Nat.le_succ n) _).trans (hYforce (n+1) i)
  have hMeanForceHere (n i : ℕ) : Uf n (u.B i) ≤ U (n+1) (u.B i) :=
    (timeJetSeminorm_unweighted_order_le hT (q-1) ℓ h (Nat.le_succ n) _).trans (hTime (n+1) _)
  have hAverage (n : ℕ) (f : VP) : Uf n (A.average f) ≤ Uf n f :=
    timeJetSeminorm_average_le hT (q-1) ℓ h n G M κ f (Subset.rfl : Icc 0 T ⊆ Icc 0 T)
      (fun _ => 1) (C := 1) (by simp)
  refine ⟨hExact, hCentered, ?_, ?_, ?_, hResidual, hRelay, ?_, ?_, ?_⟩
  · rintro n hn _ _ ⟨i,j⟩ _
    refine (hAverage n _).trans ((timeJetSeminorm_unweighted_labelAdv_le hT (q-1) G M κ
      (u.Y i) (u.Y j) ℓ h hℓ n (hrowForce n hn)).trans ?_)
    exact time_source_product_le (hSlow₀ n hn) (hSlow n hn) (apply_nonneg _ _)
      (hYForceHere n i) (apply_nonneg _ _) (hYforce (n+1) j)
  · rintro n hn _ _ ⟨i,j⟩ _
    refine (hAverage n _).trans ((timeJetSeminorm_unweighted_slowLabelDivergenceProduct_le
      hT (q-1) G (u.V i) (u.Y j) ℓ h hℓ n (hrowForce n hn)).trans ?_)
    exact time_source_product_le (hSlow₀ n hn) (hSlow n hn) (apply_nonneg _ _)
      (hVforce (n+1) i) (apply_nonneg _ _) (hYForceHere n j)
  · rintro n hn _ _ ⟨i,j⟩ _
    refine (timeJetSeminorm_unweighted_labelAdv_le hT (q-1) G M κ (u.B i) (u.B j)
      ℓ h hℓ n (hrowForce n hn)).trans ?_
    exact time_source_product_le (hSlow₀ n hn) (hSlow n hn) (apply_nonneg _ _)
      (hMeanForceHere n i) (apply_nonneg _ _) (hTime (n+1) _)
  · rintro n hn _ _ ⟨i,j⟩ _
    refine (timeJetSeminorm_centered_labelProduct_le ht₀ htT γ hγ hγpos hT q G M κ
      ℓ h hℓ n (hrow n hn) u i j hγle (hYzero j)
      (average_labelAdv_independent_independent hT G M κ _ _ hGphase (hB i) (hB j))).trans ?_
    exact mul_le_mul_of_nonneg_right (hRowCap n hn)
      (mul_nonneg (s.nonneg _ _).2.2.2.2.2.2 (s.nonneg _ _).2.2.2.2.2.2)
  · rintro n hn _ _ ⟨i,j⟩ _
    refine (timeJetSeminorm_amplitude_centered_phaseAdv_le ht₀ htT γ hγ hγpos hT q G M
      κ (u.C (i-1)) (u.Y j) ℓ h hh n hγle (hCzero (i-1))).trans ?_
    exact time_source_product_le (by positivity) (hFastCap n hn)
      (apply_nonneg _ _) le_rfl (apply_nonneg _ _) le_rfl
  · rintro n hn _ _ ⟨i,j⟩ _
    refine (timeJetSeminorm_amplitude_phaseAdv_le ht₀ htT γ hγ hγpos hT q G M
      κ (u.B i) (u.Y j) ℓ h hh n).trans ?_
    have hc : Q²(n) * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
          (scaledPhaseCoefficientProfile h κ) ≤ K * L * freq ^ (3 / 2 : ℝ) := by
      refine (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans ?_
      simpa only [mul_assoc] using hFastCap n hn
    exact time_source_product_le (by positivity) hc (apply_nonneg _ _) le_rfl
      (apply_nonneg _ _) le_rfl


set_option maxHeartbeats 1800000 in
/-- The omitted slow and fast products have the full-slab mixed bound
needed for the actual finite-depth residual. -/
theorem actualMixedMeasuredLevels_tailNonlinearBounds (hT : 0 < T) (q n : ℕ)
    (G M : MP) (κ : VP) (u : HierarchyProfiles VP SP) (P : ℕ) (completionSwitch residual : VP)
    {freq L K : ℝ} (hf : 0 ≤ freq) (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (hh : h ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hVzero : ∀ p, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.V p).val.val.val (t,x) = 0)
    (hCzero : ∀ p, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.C p).val.val.val (t,x) = 0)
    {rowCap : ℝ}
    (hrow : ∀ i : Fin 3, timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      (scaledCoframeRowProfile ℓ G i) ≤ rowCap)
    (hRowCap : 2 * (3 * Q²(n) * rowCap) ≤ K * L)
    (hFastCap : (2 * Q²(n)) * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      (scaledPhaseCoefficientProfile h κ) ≤ K * L * freq ^ (3 / 2 : ℝ)) :
    let A := twistedHierarchyOperators hT G M κ
    let U : ℕ → Seminorm ℝ VP := fun m => timeJetSeminorm hT q (unweightedSeminorm False ℓ h m hT)
    let Uf : ℕ → Seminorm ℝ VP := fun m => timeJetSeminorm hT (q - 1) (unweightedSeminorm False ℓ h m hT)
    let W : ℕ → Seminorm ℝ VP := fun m =>
      timeJetSeminorm hT q (amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hγpos)
    let Wp : ℕ → Seminorm ℝ SP := fun m =>
      timeJetSeminorm hT q (amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hγpos)
    let s := HierarchyMeasuredLevels.ofProfilesWithMeanForce A u P completionSwitch residual freq hf U Uf W Wp
    (∀ ij ∈ hierarchyTailPairs P 0,
      U n (A.labelProduct u ij) ≤ K * L * (s.Z (n+1) ij.1 * s.Z (n+1) ij.2)) ∧
    (∀ ij ∈ hierarchyTailPairs P 1,
      U n (A.completionPhaseProduct u ij) ≤ K * L * freq ^ (3 / 2 : ℝ) *
        (s.completion n (ij.1-1) * s.Y (n+1) ij.2)) ∧
    (∀ ij ∈ hierarchyTailPairs P 1,
      U n (A.meanPhaseProduct u ij) ≤ K * L * freq ^ (3 / 2 : ℝ) *
        (s.mean n ij.1 * s.Y (n+1) ij.2)) := by
  intro A U Uf W Wp s
  have hYzero (i : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (hl : t < t₀) (x : Vec3 × ℝ) :
      (u.Y i).val.val.val (t,x) = 0 := by
    change (u.V i).val.val.val (t,x) + (u.C (i-1)).val.val.val (t,x) = 0
    rw [hVzero i t ht hl x, hCzero (i-1) t ht hl x, add_zero]
  have hY (m i : ℕ) : U m (u.Y i) ≤ s.Y m i :=
    timeJetSeminorm_le_amplitude_of_inactive hT q False ℓ h m ht₀ htT γ hγ hγpos hγle _ (hYzero i)
  have hC (m i : ℕ) : U m (u.C i) ≤ s.completion m i :=
    timeJetSeminorm_le_amplitude_of_inactive hT q False ℓ h m ht₀ htT γ hγ hγpos hγle _ (hCzero i)
  have hZ (m i : ℕ) : U m (u.Z i) ≤ s.Z m i :=
    (map_add_le_add (U m) _ _).trans (add_le_add (hY m i) le_rfl)
  have hZhere (i : ℕ) : U n (u.Z i) ≤ s.Z (n+1) i :=
    (timeJetSeminorm_unweighted_order_le hT q ℓ h (Nat.le_succ n) _).trans (hZ (n+1) i)
  have hSlow₀ : 0 ≤ 3 * Q²(n) * rowCap :=
    mul_nonneg (by positivity) ((apply_nonneg _ _).trans (hrow 0))
  have hSlow : 3 * Q²(n) * rowCap ≤ K * L :=
    (le_mul_of_one_le_left hSlow₀ (by norm_num)).trans hRowCap
  let D := Q²(n) * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
    (scaledPhaseCoefficientProfile h κ)
  have hD₀ : 0 ≤ D := by dsimp only [D]; positivity
  have hD : D ≤ K * L * freq ^ (3 / 2 : ℝ) := by
    refine (le_mul_of_one_le_left hD₀ (by norm_num : (1 : ℝ) ≤ 2)).trans ?_
    simpa only [D, mul_assoc] using hFastCap
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i,j⟩ _
    refine (timeJetSeminorm_unweighted_labelAdv_le hT q G M κ (u.Z i) (u.Z j)
      ℓ h hℓ n hrow).trans ?_
    exact time_source_product_le hSlow₀ hSlow (apply_nonneg _ _) (hZhere i)
      (apply_nonneg _ _) (hZ (n+1) j)
  · rintro ⟨i,j⟩ _
    refine (timeJetSeminorm_unweighted_phaseAdv_le hT q G M κ (u.C (i-1)) (u.Y j)
      ℓ h hh n).trans ?_
    exact time_source_product_le hD₀ hD (apply_nonneg _ _) (hC n (i-1))
      (apply_nonneg _ _) (hY (n+1) j)
  · rintro ⟨i,j⟩ _
    refine (timeJetSeminorm_unweighted_phaseAdv_le hT q G M κ (u.B i) (u.Y j)
      ℓ h hh n).trans ?_
    exact time_source_product_le hD₀ hD (apply_nonneg _ _) le_rfl
      (apply_nonneg _ _) (hY (n+1) j)

end

end TorusEuler.HierarchyTwistedProfile
