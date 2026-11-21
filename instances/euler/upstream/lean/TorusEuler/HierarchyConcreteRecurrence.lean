import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyTwistedSourceCancellation

/-! The exact source and selected-solve inequalities for the measured recursion. -/

open Set

namespace TorusEuler

section Algebra

variable {E Q : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]

/-- Use the actual averaged source decomposition before applying the three
termwise slow bounds and the level-two residual bound. -/
theorem HierarchyMeasuredLevels.ofProfiles_meanForcing_of_average_eq_withResidualLoss
    (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    {P p : ℕ} (hp : p ∈ Finset.Icc 2 P) (n : ℕ) (completionSwitch residual : E)
    {freq L K : ℝ} (hf : 0 ≤ freq) (meanResidualLoss : Option ℝ)
    (U W : ℕ → Seminorm ℝ E) (pressureNorm : ℕ → Seminorm ℝ Q) (divProduct : ℕ → ℕ → E)
    (hAverage : A.average (A.sourceBeforeMean u P completionSwitch p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2)) + A.average (divProduct ij.1 ij.2) +
          A.labelAdv (u.B ij.1) (u.B ij.2))) :
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq hf
      (fun j => U j) (fun j => W j) (fun j => pressureNorm j)
      (fun j => apply_nonneg (U j)) (fun j => apply_nonneg (W j)) (fun j => apply_nonneg (pressureNorm j))
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2))) ≤
        K * L * (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.average (divProduct ij.1 ij.2)) ≤
        K * L * (s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.labelAdv (u.B ij.1) (u.B ij.2)) ≤
        K * L * (s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) →
    (p = 2 → U n residual ≤ hierarchyParentResidualConstant K meanResidualLoss * freq ^ hierarchyMeanExponent 2) →
    s.meanSource n p ≤ K * L *
      (∑ ij ∈ hierarchyLevelPairs P 0 p,
        (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) +
      (if p = 2 then hierarchyParentResidualConstant K meanResidualLoss * freq ^ hierarchyMeanExponent 2 else 0) := by
  classical
  intro s hYY hdiv hBB hR
  let N := U n
  let a (ij : ℕ × ℕ) := A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2))
  let b (ij : ℕ × ℕ) := A.average (divProduct ij.1 ij.2)
  let c (ij : ℕ × ℕ) := A.labelAdv (u.B ij.1) (u.B ij.2)
  let Pairs := hierarchyLevelPairs P 0 p
  have hp₁ : p ≠ 1 := by have := (Finset.mem_Icc.mp hp).1; omega
  have hSum : N (∑ ij ∈ Pairs, (a ij + b ij + c ij)) ≤ ∑ ij ∈ Pairs, N (a ij + b ij + c ij) := by
    let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
    exact norm_sum_le Pairs (fun ij => a ij + b ij + c ij)
  change (if p = 1 then 0 else N (-A.average (A.sourceBeforeMean u P completionSwitch p) -
    (if p = 2 then residual else 0))) ≤ _
  rw [ite_eq_right hp₁, hAverage, sub_eq_add_neg, ← neg_add, map_neg_eq_map]
  apply (map_add_le_add N _ _).trans
  apply add_le_add
  · rw [Finset.mul_sum]
    refine hSum.trans (Finset.sum_le_sum fun ij hij => ?_)
    calc
      _ ≤ N (a ij) + N (b ij) + N (c ij) :=
        (map_add_le_add N _ _).trans (add_le_add (map_add_le_add N _ _) le_rfl)
      _ ≤ _ := by
        rw [mul_add, mul_add]
        exact add_le_add (add_le_add (hYY ij hij) (hdiv ij hij)) (hBB ij hij)
  · by_cases h : p = 2
    · simpa [h] using hR h
    · simp [h]

/-- The spatial source estimate retains a unit parent-residual loss. -/
theorem HierarchyMeasuredLevels.ofProfiles_meanForcing_of_average_eq
    (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    {P p : ℕ} (hp : p ∈ Finset.Icc 2 P) (n : ℕ) (completionSwitch residual : E)
    {freq L K : ℝ} (hf : 0 ≤ freq)
    (U W : ℕ → Seminorm ℝ E) (pressureNorm : ℕ → Seminorm ℝ Q) (divProduct : ℕ → ℕ → E)
    (hAverage : A.average (A.sourceBeforeMean u P completionSwitch p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2)) + A.average (divProduct ij.1 ij.2) +
          A.labelAdv (u.B ij.1) (u.B ij.2))) :
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq hf
      (fun j => U j) (fun j => W j) (fun j => pressureNorm j)
      (fun j => apply_nonneg (U j)) (fun j => apply_nonneg (W j)) (fun j => apply_nonneg (pressureNorm j))
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2))) ≤
        K * L * (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.average (divProduct ij.1 ij.2)) ≤
        K * L * (s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.labelAdv (u.B ij.1) (u.B ij.2)) ≤
        K * L * (s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) →
    (p = 2 → U n residual ≤ K * freq ^ hierarchyMeanExponent 2) →
    s.meanSource n p ≤ K * L *
      (∑ ij ∈ hierarchyLevelPairs P 0 p,
        (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) +
      (if p = 2 then K * freq ^ hierarchyMeanExponent 2 else 0) :=
  HierarchyMeasuredLevels.ofProfiles_meanForcing_of_average_eq_withResidualLoss
    A u hp n completionSwitch residual hf none U W pressureNorm divProduct hAverage

/-- Extract the exact selected mean solution and its forcing norm. -/
theorem FiniteHierarchySolvers.construct_meanSolve_bound {A : HierarchyOperators E Q}
    (S : FiniteHierarchySolvers A) {P p : ℕ} (hp : p ∈ Finset.Icc 2 P)
    (completionSwitch residual : E) (hR : A.average residual = residual)
    (leading : HierarchyTransverseOutput A) {freq L : ℝ} (hf : 0 ≤ freq)
    (U W : ℕ → Seminorm ℝ E) (pressureNorm : ℕ → Seminorm ℝ Q) (n : ℕ)
    (hSolve : ∀ f hf, U n (S.solveMean f hf).val.B ≤ L * U (n + 1) f) :
    let u := S.construct P completionSwitch residual hR leading
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq hf
      (fun j => U j) (fun j => W j) (fun j => pressureNorm j)
      (fun j => apply_nonneg (U j)) (fun j => apply_nonneg (W j)) (fun j => apply_nonneg (pressureNorm j))
    s.mean n p ≤ L * s.meanSource (n + 1) p := by
  intro u s
  let H := A.sourceBeforeMean u P completionSwitch p
  let f := -A.average H - (if p = 2 then residual else 0)
  obtain ⟨hf', heq, _⟩ := S.construct_mean_selected hp completionSwitch residual hR leading
  change u.B p = (S.solveMean f hf').val.B at heq
  have hp₁ : p ≠ 1 := by have := (Finset.mem_Icc.mp hp).1; omega
  change U n (u.B p) ≤ L * (if p = 1 then 0 else U (n + 1) f)
  rw [heq, ite_eq_right hp₁]
  exact hSolve f hf'

/-- The two seed-zero conditions are exact for the selected finite recursion. -/
theorem FiniteHierarchySolvers.construct_measured_seedZeros {A : HierarchyOperators E Q}
    (S : FiniteHierarchySolvers A) {P : ℕ} (hP : 1 ≤ P)
    (completionSwitch residual : E) (hR : A.average residual = residual)
    (leading : HierarchyTransverseOutput A) {freq : ℝ} (hf : 0 ≤ freq)
    (U W : ℕ → Seminorm ℝ E) (pressureNorm : ℕ → Seminorm ℝ Q) (n : ℕ) :
    let u := S.construct P completionSwitch residual hR leading
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq hf
      (fun j => U j) (fun j => W j) (fun j => pressureNorm j)
      (fun j => apply_nonneg (U j)) (fun j => apply_nonneg (W j)) (fun j => apply_nonneg (pressureNorm j))
    s.oscSource n 1 = 0 ∧ s.meanSource n 1 = 0 ∧ s.mean n 1 = 0 ∧ s.completion n 0 = 0 := by
  intro u s
  obtain ⟨_, _, hB, _⟩ := S.construct_leading P completionSwitch residual hR leading
  obtain ⟨_, hC, _, _, _⟩ := S.construct_eq_zero_of_index hP (.inl rfl)
    completionSwitch residual hR leading
  change u.B 1 = 0 at hB
  change u.C 0 = 0 at hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [s, HierarchyMeasuredLevels.ofProfiles]
  · simp [s, HierarchyMeasuredLevels.ofProfiles]
  · change U n (u.B 1) = 0
    rw [hB, map_zero]
  · change W n (u.C 0) = 0
    rw [hC, map_zero]

/-- Individual retained source estimates, with the same parent power for
all derivative orders and levels. -/
structure HierarchySourceTermBounds (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    (completionSwitch residual : E) (divProduct : ℕ → ℕ → E)
    (U W : ℕ → Seminorm ℝ E) (s : HierarchyMeasuredLevels) (freq L K : ℝ) (P H : ℕ)
    (meanResidualLoss : Option ℝ := none) : Prop where
  mean_exact : ∀ p ∈ Finset.Icc 2 P, A.average (A.sourceBeforeMean u P completionSwitch p) =
    ∑ ij ∈ hierarchyLevelPairs P 0 p,
      (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2)) + A.average (divProduct ij.1 ij.2) +
        A.labelAdv (u.B ij.1) (u.B ij.2))
  relay_centered : ∀ p ∈ Finset.Icc 2 P, A.average (A.relayAtLevel u completionSwitch p) = 0
  mean_YY : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
    U n (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2))) ≤ K * L *
      (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2)
  mean_divY : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
    U n (A.average (divProduct ij.1 ij.2)) ≤ K * L * (s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2)
  mean_BB : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
    U n (A.labelAdv (u.B ij.1) (u.B ij.2)) ≤ K * L * (s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)
  residual_bound : ∀ n, n + 1 ≤ H → U n residual ≤
    hierarchyParentResidualConstant K meanResidualLoss * freq ^ hierarchyMeanExponent 2
  relay_bound : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P,
    W n (A.relayAtLevel u completionSwitch p) ≤ K * L *
      (freq ^ (-1 : ℝ) * (s.osc (n + 1) (p - 1) + s.oscSource (n + 1) (p - 1)))
  slow_centered : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
    W n (A.labelProduct u ij - A.average (A.labelProduct u ij)) ≤
      K * L * (s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2)
  fast_completion : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 1 p,
    W n (A.completionPhaseProduct u ij - A.average (A.completionPhaseProduct u ij)) ≤
      (K * L * freq ^ (3 / 2 : ℝ)) * (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2)
  fast_mean : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 1 p,
    W n (A.meanPhaseProduct u ij) ≤
      (K * L * freq ^ (3 / 2 : ℝ)) * (s.mean n ij.1 * s.Y (n + 1) ij.2)

set_option maxHeartbeats 2600000 in
/-- The selected construction satisfies the quantitative recurrence from
its linear solves and the individual source bounds. -/
theorem FiniteHierarchySolvers.construct_normRecurrence_from_terms {A : HierarchyOperators E Q}
    (S : FiniteHierarchySolvers A) {P H : ℕ} (hP : 1 ≤ P)
    (completionSwitch residual : E) (hR : A.average residual = residual)
    (leading : HierarchyTransverseOutput A) {freq L K : ℝ} (hf : 0 ≤ freq) (hL : 0 ≤ L)
    (hK : 0 ≤ K) (U W : ℕ → Seminorm ℝ E) (pressureNorm : ℕ → Seminorm ℝ Q)
    (divProduct : ℕ → ℕ → E)
    (hSeed : ∀ n ≤ H, W n leading.V + freq * pressureNorm n leading.p ≤
      K * L * freq ^ hierarchyOscExponent 1)
    (hMean : ∀ n, n + 1 ≤ H → ∀ f hf, U n (S.solveMean f hf).val.B ≤ K * L * U (n + 1) f)
    (hComplete : ∀ n, n + 1 ≤ H → ∀ v, A.average v = 0 →
      W n (S.complete v) ≤ K * L * freq ^ (-1 : ℝ) * W (n + 1) v) :
    let u := S.construct P completionSwitch residual hR leading
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq hf
      (fun j => U j) (fun j => W j) (fun j => pressureNorm j)
      (fun j => apply_nonneg (U j)) (fun j => apply_nonneg (W j)) (fun j => apply_nonneg (pressureNorm j))
    (∀ n ≤ H, ∀ p ∈ Finset.Icc 2 P, s.osc n p ≤ K * L * s.oscSource n p) →
    HierarchySourceTermBounds A u completionSwitch residual divProduct U W s freq L K P H →
    HierarchyNormRecurrence s freq L K P H := by
  intro u s hOsc hTerms
  obtain ⟨hV, hp, _, _⟩ := S.construct_leading P completionSwitch residual hR leading
  change u.V 1 = leading.V at hV
  change u.p 1 = leading.p at hp
  have hChosenMean : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P,
      s.mean n p ≤ K * L * s.meanSource (n + 1) p := by
    intro n hn p hpm
    exact S.construct_meanSolve_bound hpm completionSwitch residual hR leading hf U W pressureNorm n (hMean n hn)
  have htransverse (p : ℕ) (hpm : p ∈ Finset.Icc 1 P) : A.average (u.V p) = 0 := by
    by_cases h₁ : p = 1
    · subst p
      rw [hV]
      exact leading.average_V
    · have hpy : p ∈ Finset.Icc 2 P := by
        obtain ⟨hp₁, hpP⟩ := Finset.mem_Icc.mp hpm
        exact Finset.mem_Icc.mpr ⟨by omega, hpP⟩
      obtain ⟨hs, hv, _⟩ := S.construct_transverse_selected hpy completionSwitch residual hR leading
      change u.V p = _ at hv
      rw [hv]
      exact (S.solveTransverse _ hs).val.average_V
  refine ⟨?_, S.construct_measured_seedZeros hP completionSwitch residual hR leading hf U W pressureNorm,
    ?_, hChosenMean, ?_, hOsc, ?_, ?_, ?_⟩
  · intro n hn
    change W n (u.V 1) + freq * pressureNorm n (u.p 1) ≤ _
    rw [hV, hp]
    exact hSeed n hn
  · intro n hn p hpm
    exact HierarchyMeasuredLevels.ofProfiles_meanForcing_of_average_eq A u hpm n completionSwitch residual
      hf U W pressureNorm divProduct (hTerms.mean_exact p hpm) (hTerms.mean_YY n hn p hpm)
      (hTerms.mean_divY n hn p hpm) (hTerms.mean_BB n hn p hpm) (fun _ => hTerms.residual_bound n hn)
  · intro n hn p hpm
    exact HierarchyMeasuredLevels.ofProfiles_oscForcing A u hpm n completionSwitch residual hf U W
      (fun j => pressureNorm j) (fun j => apply_nonneg (pressureNorm j)) (hTerms.relay_centered p hpm)
      (hTerms.relay_bound n hn p hpm) (hTerms.slow_centered n hn p hpm) (hTerms.fast_completion n hn p hpm)
      (hTerms.fast_mean n hn p hpm)
  · intro n hn p hpm
    have hc := S.construct_completion hpm completionSwitch residual hR leading
    change u.C p = S.complete (u.V p) at hc
    change W n (u.C p) ≤ K * L * freq ^ (-1 : ℝ) * (W (n + 1) (u.V p) + freq * pressureNorm (n+1) (u.p p))
    rw [hc]
    exact (hComplete n hn _ (htransverse p hpm)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hf (apply_nonneg _ _))) (by positivity))
  · intro n _ p _
    change W n (u.V p + u.C (p - 1)) ≤ W n (u.V p) + freq * pressureNorm n (u.p p) + W n (u.C (p - 1))
    exact (map_add_le_add (W n) _ _).trans
      (add_le_add (le_add_of_nonneg_right (mul_nonneg hf (apply_nonneg _ _))) le_rfl)
  · intros
    rfl

end Algebra

end TorusEuler
