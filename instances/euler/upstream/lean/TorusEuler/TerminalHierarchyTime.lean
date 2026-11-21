import TorusEuler.HierarchyConcreteRecurrence
import TorusEuler.HierarchyDepthTail

/-! The finite hierarchy with separate time orders for mean velocity and its force. -/

namespace TorusEuler

noncomputable section

variable {E Q : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]

/-- Measure the mean source one time order below the mean velocity. All
other rows use the ordinary profile measurements. -/
def HierarchyMeasuredLevels.ofProfilesWithMeanForce
    (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q) (P : ℕ)
    (completionSwitch residual : E) (freq : ℝ) (hf : 0 ≤ freq)
    (U Uforce W : ℕ → Seminorm ℝ E) (Wpressure : ℕ → Seminorm ℝ Q) : HierarchyMeasuredLevels :=
  let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq hf (fun n => U n) (fun n => W n) (fun n => Wpressure n)
      (fun n => apply_nonneg (U n)) (fun n => apply_nonneg (W n))
      (fun n => apply_nonneg (Wpressure n))
  let sforce := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq hf (fun n => Uforce n) (fun n => W n) (fun n => Wpressure n)
      (fun n => apply_nonneg (Uforce n)) (fun n => apply_nonneg (W n))
      (fun n => apply_nonneg (Wpressure n))
  { s with
    meanSource := sforce.meanSource
    nonneg := fun n p => ⟨(s.nonneg n p).1, (sforce.nonneg n p).2.1, (s.nonneg n p).2.2⟩ }

set_option maxHeartbeats 2200000 in
/-- The mixed quantitative recurrence applies to the actual selected
hierarchy. In the mean-source terms the complete field is measured at
the higher order, while the force and the old residual use the lower
seminorm. Thus the lower-order residual estimate suffices. -/
theorem FiniteHierarchySolvers.construct_normRecurrence_withMeanForce
    {A : HierarchyOperators E Q} (S : FiniteHierarchySolvers A) {P H : ℕ} (hP : 1 ≤ P)
    (completionSwitch residual : E) (hR : A.average residual = residual)
    (leading : HierarchyTransverseOutput A) {freq L K : ℝ} (hf : 0 ≤ freq)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (U Uforce W : ℕ → Seminorm ℝ E)
    (Wpressure : ℕ → Seminorm ℝ Q) (divProduct : ℕ → ℕ → E)
    (hSeed : ∀ n ≤ H, W n leading.V + freq * Wpressure n leading.p ≤
      K * L * freq ^ hierarchyOscExponent 1)
    (hMean : ∀ n, n + 1 ≤ H → ∀ f hf', U n (S.solveMean f hf').val.B ≤ K * L * Uforce (n + 1) f)
    (hComplete : ∀ n, n + 1 ≤ H → ∀ v, A.average v = 0 →
      W n (S.complete v) ≤ K * L * freq ^ (-1 : ℝ) * W (n + 1) v) :
    let u := S.construct P completionSwitch residual hR leading
    let s := HierarchyMeasuredLevels.ofProfilesWithMeanForce A u P completionSwitch residual freq hf U Uforce W Wpressure
    (∀ n ≤ H, ∀ p ∈ Finset.Icc 2 P, s.osc n p ≤ K * L * s.oscSource n p) →
    HierarchySourceTermBounds A u completionSwitch residual divProduct Uforce W s freq L K P H (some L) →
    HierarchyNormRecurrence s freq L K P H (some L) := by
  intro u s hOsc hTerms
  obtain ⟨hV, hp, _, _⟩ := S.construct_leading P completionSwitch residual hR leading
  change u.V 1 = leading.V at hV
  change u.p 1 = leading.p at hp
  have htransverse (p : ℕ) (hpm : p ∈ Finset.Icc 1 P) : A.average (u.V p) = 0 := by
    by_cases h₁ : p = 1
    · subst p
      rw [hV]
      exact leading.average_V
    · have hpy : p ∈ Finset.Icc 2 P := by
        obtain ⟨hmin, hmax⟩ := Finset.mem_Icc.mp hpm
        exact Finset.mem_Icc.mpr ⟨by omega, hmax⟩
      obtain ⟨hs, hv, _⟩ := S.construct_transverse_selected hpy completionSwitch residual hR leading
      change u.V p = _ at hv
      rw [hv]
      exact (S.solveTransverse _ hs).val.average_V
  refine ⟨?_, ?_, ?_, ?_, ?_, hOsc, ?_, ?_, ?_⟩
  · intro n hn
    change W n (u.V 1) + freq * Wpressure n (u.p 1) ≤ _
    rw [hV, hp]
    exact hSeed n hn
  · intro n
    exact S.construct_measured_seedZeros hP completionSwitch residual hR leading hf U W Wpressure n
  · intro n hn p hpm
    let meanNorm (m : ℕ) := if m = n then Uforce m else U m
    have hnext : n + 1 ≠ n := by omega
    have hYY := hTerms.mean_YY n hn p hpm
    have hdiv := hTerms.mean_divY n hn p hpm
    have hBB := hTerms.mean_BB n hn p hpm
    have hrest := hTerms.residual_bound n hn
    have h := HierarchyMeasuredLevels.ofProfiles_meanForcing_of_average_eq_withResidualLoss A u hpm n completionSwitch
      residual hf (some L) meanNorm W Wpressure divProduct (hTerms.mean_exact p hpm)
      (by simpa [meanNorm, hnext, HierarchyMeasuredLevels.ofProfilesWithMeanForce,
        HierarchyMeasuredLevels.ofProfiles, s] using hYY)
      (by simpa [meanNorm, hnext, HierarchyMeasuredLevels.ofProfilesWithMeanForce,
        HierarchyMeasuredLevels.ofProfiles, s] using hdiv)
      (by simpa [meanNorm, hnext, HierarchyMeasuredLevels.ofProfilesWithMeanForce,
        HierarchyMeasuredLevels.ofProfiles, s] using hBB)
      (fun _ => by simpa [meanNorm] using hrest)
    simpa [meanNorm, hnext, HierarchyMeasuredLevels.ofProfilesWithMeanForce,
      HierarchyMeasuredLevels.ofProfiles, s] using h
  · intro n hn p hpm
    let f := -A.average (A.sourceBeforeMean u P completionSwitch p) - (if p = 2 then residual else 0)
    obtain ⟨hf', heq, _⟩ := S.construct_mean_selected hpm completionSwitch residual hR leading
    change u.B p = (S.solveMean f hf').val.B at heq
    have hp₁ : p ≠ 1 := by have := (Finset.mem_Icc.mp hpm).1; omega
    change U n (u.B p) ≤ K * L * (if p = 1 then 0 else Uforce (n + 1) f)
    rw [heq, ite_eq_right hp₁]
    exact hMean n hn f hf'
  · intro n hn p hpm
    exact HierarchyMeasuredLevels.ofProfiles_oscForcing A u hpm n completionSwitch residual hf U W (fun n => Wpressure n)
      (fun n => apply_nonneg (Wpressure n)) (hTerms.relay_centered p hpm)
      (hTerms.relay_bound n hn p hpm) (hTerms.slow_centered n hn p hpm)
      (hTerms.fast_completion n hn p hpm) (hTerms.fast_mean n hn p hpm)
  · intro n hn p hpm
    have hc := S.construct_completion hpm completionSwitch residual hR leading
    change u.C p = S.complete (u.V p) at hc
    change W n (u.C p) ≤ K * L * freq ^ (-1 : ℝ) *
      (W (n + 1) (u.V p) + freq * Wpressure (n + 1) (u.p p))
    rw [hc]
    exact (hComplete n hn _ (htransverse p hpm)).trans
      (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hf (apply_nonneg _ _))) (by positivity))
  · intro n _ p _
    change W n (u.V p + u.C (p - 1)) ≤ W n (u.V p) + freq * Wpressure n (u.p p) +
      W n (u.C (p - 1))
    exact (map_add_le_add (W n) _ _).trans
      (add_le_add (le_add_of_nonneg_right (mul_nonneg hf (apply_nonneg _ _))) le_rfl)
  · intros
    rfl

private theorem hierarchy_time_norm_sum_le {ι : Type*} (N : Seminorm ℝ E)
    (s : Finset ι) (f : ι → E) : N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
  exact norm_sum_le s f

set_option maxHeartbeats 1800000 in
/-- On the exact finite expansion, the mean-force measurement affects
neither the mean nor the oscillatory velocity sum. -/
theorem FiniteHierarchySolvers.velocity_sums_withMeanForce
    {A : HierarchyOperators E Q} (S : FiniteHierarchySolvers A) {P : ℕ}
    (completionSwitch residual : E) (hR : A.average residual = residual)
    (leading : HierarchyTransverseOutput A) {freq L C : ℝ}
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (U Uforce W : ℕ → Seminorm ℝ E) (Wpressure : ℕ → Seminorm ℝ Q) (n : ℕ) :
    let u := S.construct P completionSwitch residual hR leading
    let s := HierarchyMeasuredLevels.ofProfilesWithMeanForce A u P completionSwitch residual
      freq (zero_le_one.trans hf) U Uforce W Wpressure
    (∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound s freq L C n i) →
    let depthCount := ((Finset.Icc 1 P).card : ℝ)
    W n (u.velocity P - A.average (u.velocity P)) ≤ 2 * depthCount * C * L ^ 2 * freq ^ (-5 / 4 : ℝ) ∧
      U n (A.average (u.velocity P)) ≤ depthCount * C * L ^ 6 * freq ^ (-5 / 2 : ℝ) := by
  classical
  intro u s hlevels depthCount
  let levels := Finset.Icc 1 P
  have hOsc : u.velocity P - A.average (u.velocity P) = ∑ i ∈ levels, (u.V i + u.C i) :=
    S.construct_velocity_sub_average P completionSwitch residual hR leading
  have hMean : A.average (u.velocity P) = ∑ i ∈ levels, u.B i := by
    have hSum : u.velocity P = (∑ i ∈ levels, (u.V i + u.C i)) + ∑ i ∈ levels, u.B i :=
      Finset.sum_add_distrib
    rw [show A.average (u.velocity P) = u.velocity P - (u.velocity P - A.average (u.velocity P)) by abel,
      hOsc, hSum, add_sub_cancel_left]
  have hOscExponent (i : ℕ) (hi : 1 ≤ i) : hierarchyOscExponent i ≤ (-5 / 4 : ℝ) := by
    exact (hierarchyOscExponent_antitone hi).trans_eq (by norm_num [hierarchyOscExponent])
  have hf₀ : 0 ≤ freq := zero_le_one.trans hf
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hV (i : ℕ) (hi : i ∈ levels) : W n (u.V i) ≤ C * L ^ 2 * freq ^ (-5 / 4 : ℝ) := by
    have h := (hlevels i hi).osc
    change W n (u.V i) + freq * Wpressure n (u.p i) ≤ _ at h
    refine ((le_add_of_nonneg_right (mul_nonneg hf₀ (apply_nonneg _ _))).trans h).trans ?_
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hL₀ (sub_nonneg.mpr hL)]) hC
    · exact Real.rpow_le_rpow_of_exponent_le hf (hOscExponent i (Finset.mem_Icc.mp hi).1)
    · positivity
    · positivity
  have hCompletion (i : ℕ) (hi : i ∈ levels) : W n (u.C i) ≤ C * L ^ 2 * freq ^ (-5 / 4 : ℝ) := by
    refine (hlevels i hi).completion.trans ?_
    have he : hierarchyCompletionExponent i ≤ (-5 / 4 : ℝ) :=
      (sub_le_self _ zero_le_one).trans (hOscExponent i (Finset.mem_Icc.mp hi).1)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hf he) (by positivity)
  have hB (i : ℕ) (hi : i ∈ levels) : U n (u.B i) ≤ C * L ^ 6 * freq ^ (-5 / 2 : ℝ) := by
    by_cases hOne : i = 1
    · have hzero : u.B 1 = 0 := (S.construct_leading P completionSwitch residual hR leading).2.2.1
      rw [hOne, hzero, map_zero]
      positivity
    · have hi₂ : 2 ≤ i := by have := (Finset.mem_Icc.mp hi).1; omega
      have hcast : (2 : ℝ) ≤ i := by exact_mod_cast hi₂
      have he : hierarchyMeanExponent i ≤ (-5 / 2 : ℝ) := by
        unfold hierarchyMeanExponent
        linarith
      exact (hlevels i hi).meanStrong.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hf he) (by positivity))
  rw [hOsc, hMean]
  constructor
  · refine (hierarchy_time_norm_sum_le _ _ _).trans ?_
    calc
      _ ≤ ∑ _i ∈ levels, 2 * (C * L ^ 2 * freq ^ (-5 / 4 : ℝ)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [two_mul]
        exact (map_add_le_add (W n) _ _).trans (add_le_add (hV i hi) (hCompletion i hi))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; dsimp [depthCount, levels]; ring
  · refine (hierarchy_time_norm_sum_le _ _ _).trans ?_
    calc
      _ ≤ ∑ _i ∈ levels, C * L ^ 6 * freq ^ (-5 / 2 : ℝ) := Finset.sum_le_sum hB
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; dsimp [depthCount, levels]; ring

set_option maxHeartbeats 1800000 in
/-- The unweighted mixed-time remainder retains the level-`P+1`
frequency gain. The exact endpoint of the retained expansion supplies
the level-`P+1` profiles used by its quadratic tails. -/
theorem FiniteHierarchySolvers.remainder_withMeanForce
    {A : HierarchyOperators E Q} (S : FiniteHierarchySolvers A) {P : ℕ} (hP : 1 ≤ P)
    (completionSwitch residual : E) (hR : A.average residual = residual)
    (leading : HierarchyTransverseOutput A) {freq L K C : ℝ}
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (U Uforce W : ℕ → Seminorm ℝ E) (Wpressure : ℕ → Seminorm ℝ Q) (n : ℕ)
    (hU : ∀ f, U n f ≤ U (n + 1) f) (hW : ∀ f, W n f ≤ W (n + 1) f) :
    let u := S.construct P completionSwitch residual hR leading
    let s := HierarchyMeasuredLevels.ofProfilesWithMeanForce A u P completionSwitch residual
      freq (zero_le_one.trans hf) U Uforce W Wpressure
    (∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound s freq L C (n + 1) i) →
    (U n (A.material (u.C P) + A.labelGrad (u.p P)) ≤ K * L * freq ^ (-1 : ℝ) *
      (s.osc (n + 1) P + s.oscSource (n + 1) P)) →
    (∀ ij ∈ hierarchyTailPairs P 0,
      U n (A.labelProduct u ij) ≤ K * L * (s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyTailPairs P 1,
      U n (A.completionPhaseProduct u ij) ≤ K * L * freq ^ (3 / 2 : ℝ) *
        (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyTailPairs P 1,
      U n (A.meanPhaseProduct u ij) ≤ K * L * freq ^ (3 / 2 : ℝ) *
        (s.mean n ij.1 * s.Y (n + 1) ij.2)) →
    U n (A.remainder u P) ≤ 2 * K * (C + 1) ^ 2 *
      (1 + ((hierarchyTailPairs P 0).card : ℝ) + 2 * ((hierarchyTailPairs P 1).card : ℝ)) *
        freq ^ hierarchyOscExponent (P + 1) := by
  intro u s hLevel hLinear hSlow hFastCompletion hFastMean
  obtain ⟨hVlast, _, hBlast, _, _⟩ := S.construct_eq_zero_of_index hP
    (p := P + 1) (Or.inr (Nat.lt_succ_self P)) completionSwitch residual hR leading
  change u.V (P + 1) = 0 at hVlast
  change u.B (P + 1) = 0 at hBlast
  have hYlast : u.Y (P + 1) = u.C P := by
    change u.V (P + 1) + u.C (P + 1 - 1) = u.C P
    rw [Nat.add_sub_cancel, hVlast, zero_add]
  have hcompletion (i : ℕ) (hi : i ∈ Finset.Icc 1 P) :
      s.completion n i ≤ C * L ^ 2 * freq ^ hierarchyCompletionExponent i :=
    (hW (u.C i)).trans (hLevel i hi).completion
  have hmean (i : ℕ) (hi : i ∈ Finset.Icc 2 (P + 1)) :
      s.mean n i ≤ C * freq ^ hierarchyInductiveMeanExponent i := by
    obtain ⟨hmin, hmax⟩ := Finset.mem_Icc.mp hi
    by_cases h : i ≤ P
    · exact (hU (u.B i)).trans (hLevel i (Finset.mem_Icc.mpr ⟨by omega, h⟩)).mean
    · have hlast : i = P + 1 := by omega
      change U n (u.B i) ≤ _
      rw [hlast, hBlast, map_zero]
      positivity
  refine hierarchy_depth_tail_of_measuredProducts A u s P n (U n) hf hL hK hC hsmall
    hP hLevel hcompletion hmean ?_ ?_ hLinear hSlow hFastCompletion hFastMean
  · change W (n + 1) (u.Y (P + 1)) ≤ W (n + 1) (u.C P)
    rw [hYlast]
  · change W (n + 1) (u.Y (P + 1)) + U (n + 1) (u.B (P + 1)) ≤ W (n + 1) (u.C P)
    rw [hYlast, hBlast, map_zero, add_zero]

end

end TorusEuler
