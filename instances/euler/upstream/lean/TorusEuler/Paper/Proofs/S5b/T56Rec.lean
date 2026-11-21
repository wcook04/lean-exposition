import TorusEuler.HierarchyConcreteRecurrence
import TorusEuler.HierarchySourceAssembly
import TorusEuler.HierarchyFiniteOrderBudget
import TorusEuler.Paper.Proofs.S5b.T56Bounds

/-!
# Theorem 5.6, glue: the measured recurrence of an expansion

The level induction of the proof of Theorem 5.6 (`sections/06c_finite_hierarchy.tex:521-637`)
is run through the library's abstract recurrence `HierarchyNormRecurrence` and its solution
`hierarchy_level_bounds` (arithmetic of the exponents `-5/4 - 2(p-1)/3`, `-5/2 - 2(p-2)/3`, …).
This file assembles the recurrence from the individual estimates, for any family of profiles:

* `measuredLevels'`: the measured levels of the library (`HierarchyMeasuredLevels.ofProfiles`)
  with the level-one oscillation replaced by a larger quantity (in the proof, the norms of the
  unswitched leading pair `A₁`, `𝗉[A₁]`: "for `p = 2` this is the bound for `A₁`, with `f = 0`
  and `χ̃ ≤ 1`", TeX :570-571);
* `oscForcing_gen`: the oscillatory source bound with an arbitrary bound for the linear term
  (adapted from the library glue `HierarchyMeasuredLevels.ofProfiles_oscForcing`);
* `normRecurrence'`: the recurrence from the term bounds.
-/

open Set

namespace TorusEuler.Paper.S5b

noncomputable section

section Algebra

variable {E Q : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]

/-- The measured levels with the level-one oscillation replaced by `osc₁`. -/
def measuredLevels' (s : HierarchyMeasuredLevels) (osc₁ : ℕ → ℝ) (h₁ : ∀ n, 0 ≤ osc₁ n) :
    HierarchyMeasuredLevels where
  oscSource := s.oscSource
  meanSource := s.meanSource
  osc n p := if p = 1 then osc₁ n else s.osc n p
  mean := s.mean
  completion := s.completion
  Y := s.Y
  Z := s.Z
  nonneg n p := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := s.nonneg n p
    refine ⟨h1, h2, ?_, h4, h5, h6, h7⟩
    split_ifs
    · exact h₁ n
    · exact h3

/-- Oscillation bound for the reindexed measured levels. -/
theorem measuredLevels'_osc_le (s : HierarchyMeasuredLevels) (osc₁ : ℕ → ℝ) (h₁ : ∀ n, 0 ≤ osc₁ n)
    (hle : ∀ n, s.osc n 1 ≤ osc₁ n) (n p : ℕ) : s.osc n p ≤ (measuredLevels' s osc₁ h₁).osc n p := by
  change s.osc n p ≤ if p = 1 then osc₁ n else s.osc n p
  split_ifs with hp
  · subst hp; exact hle n
  · exact le_rfl

/-- Oscillation of the reindexed measured levels away from the distinguished index. -/
theorem measuredLevels'_osc_of_ne (s : HierarchyMeasuredLevels) (osc₁ : ℕ → ℝ)
    (h₁ : ∀ n, 0 ≤ osc₁ n) {p : ℕ} (hp : p ≠ 1) (n : ℕ) :
    (measuredLevels' s osc₁ h₁).osc n p = s.osc n p := by
  change (if p = 1 then osc₁ n else s.osc n p) = _
  exact ite_eq_right_iff.mpr (fun h => absurd h hp)

/-- A seminorm of a finite sum (copy of the private library lemma
`hierarchy_seminorm_finset_le`, `TorusEuler/HierarchySourceAssembly.lean:309`). -/
theorem seminorm_finset_le {I : Type*} (N : Seminorm ℝ E) (s : Finset I) (F : I → E) (b : I → ℝ)
    (hb : ∀ i ∈ s, N (F i) ≤ b i) : N (∑ i ∈ s, F i) ≤ ∑ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (map_add_le_add N _ _).trans (add_le_add
      (hb _ (Finset.mem_insert_self _ _)) (ih fun j hj => hb _ (Finset.mem_insert_of_mem hj)))

/-- **The oscillatory source bound** (`06c_finite_hierarchy.tex:563-590`): the source of
level `p` is the centered sum of the linear term, the label products and the completion phase
products, plus the mean phase products; with a bound `K L R` for the linear term (adapted from
the library glue `HierarchyMeasuredLevels.ofProfiles_oscForcing`,
`TorusEuler/HierarchySourceAssembly.lean:384`, where `R` is fixed to
`freq⁻¹ (s.osc + s.oscSource)` at level `p - 1`). -/
theorem oscForcing_gen (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    {P p : ℕ} (hp : p ∈ Finset.Icc 2 P) (n : ℕ)
    (completionSwitch parentResidual : E) {freq L K : ℝ} (hf : 0 ≤ freq)
    (unweighted weighted : ℕ → Seminorm ℝ E) (pressureWeighted : ℕ → Q → ℝ)
    (hq : ∀ m a, 0 ≤ pressureWeighted m a)
    (hrelayMean : A.average (A.relayAtLevel u completionSwitch p) = 0) (R : ℝ) :
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch parentResidual freq hf
      (fun m => unweighted m) (fun m => weighted m) pressureWeighted
      (fun m => apply_nonneg (unweighted m)) (fun m => apply_nonneg (weighted m)) hq
    (weighted n (A.relayAtLevel u completionSwitch p) ≤ K * L * R) →
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      weighted n (A.labelProduct u ij - A.average (A.labelProduct u ij)) ≤
        K * L * (s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 1 p,
      weighted n (A.completionPhaseProduct u ij - A.average (A.completionPhaseProduct u ij)) ≤
        (K * L * freq ^ (3 / 2 : ℝ)) * (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 1 p,
      weighted n (A.meanPhaseProduct u ij) ≤
        (K * L * freq ^ (3 / 2 : ℝ)) * (s.mean n ij.1 * s.Y (n + 1) ij.2)) →
    s.oscSource n p ≤ K * L *
      (R + (∑ ij ∈ hierarchyLevelPairs P 0 p, s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2) +
      freq ^ (3 / 2 : ℝ) * (∑ ij ∈ hierarchyLevelPairs P 1 p,
        (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2 +
          s.mean n ij.1 * s.Y (n + 1) ij.2))) := by
  dsimp only
  intro hrelay hslow hfast hmean
  let N := weighted n
  have hp₁ : p ≠ 1 := by have h := (Finset.mem_Icc.mp hp).1; omega
  change (if p = 1 then 0 else N
    (-(A.sourceBeforeMean u P completionSwitch p -
      A.average (A.sourceBeforeMean u P completionSwitch p)) -
      hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u))) ≤ _
  rw [ite_eq_right hp₁, sub_eq_add_neg, ← neg_add, map_neg_eq_map]
  change N (((LinearMap.id : E →ₗ[ℝ] E) - A.average)
    (A.relayAtLevel u completionSwitch p +
      (∑ ij ∈ hierarchyLevelPairs P 0 p, A.labelProduct u ij) +
      (∑ ij ∈ hierarchyLevelPairs P 1 p, A.completionPhaseProduct u ij)) +
    (∑ ij ∈ hierarchyLevelPairs P 1 p, A.meanPhaseProduct u ij)) ≤ _
  simp only [map_add, map_sum, LinearMap.sub_apply, LinearMap.id_apply, hrelayMean, sub_zero]
  rw [add_assoc (A.relayAtLevel u completionSwitch p + _), ← Finset.sum_add_distrib]
  conv_rhs => rw [mul_add, mul_add]
  apply (map_add_le_add N _ _).trans
  apply add_le_add
  · rw [Finset.mul_sum]
    exact (map_add_le_add N _ _).trans
      (add_le_add hrelay (seminorm_finset_le N _ _ _ hslow))
  · rw [← mul_assoc, Finset.mul_sum]
    apply seminorm_finset_le
    intro ij hij
    rw [mul_add]
    exact (map_add_le_add N _ _).trans (add_le_add (hfast ij hij) (hmean ij hij))

set_option maxHeartbeats 1000000 in
/-- **The measured recurrence from the term bounds** (the induction of
`06c_finite_hierarchy.tex:521-637` in the library's bookkeeping): the levels `s'` (with the
level-one oscillation `osc₁`) satisfy `HierarchyNormRecurrence` once the seed, the mean and
oscillatory source terms, the two solves, the completion and the level-one triangle
inequality are bounded. -/
theorem normRecurrence' (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q) {P H : ℕ}
    (completionSwitch residual : E) {freq L K : ℝ} (hf : 0 ≤ freq)
    (U W : ℕ → Seminorm ℝ E) (pW : ℕ → Seminorm ℝ Q) (divProduct : ℕ → ℕ → E)
    (osc₁ : ℕ → ℝ) (h₁ : ∀ n, 0 ≤ osc₁ n) (hKL : 0 ≤ K * L) :
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq hf
      (fun j => U j) (fun j => W j) (fun j => pW j)
      (fun j => apply_nonneg (U j)) (fun j => apply_nonneg (W j)) (fun j => apply_nonneg (pW j))
    let s' := measuredLevels' s osc₁ h₁
    (∀ n, s.osc n 1 ≤ osc₁ n) →
    (∀ n ≤ H, osc₁ n ≤ K * L * freq ^ hierarchyOscExponent 1) →
    u.B 1 = 0 → u.C 0 = 0 →
    (∀ p ∈ Finset.Icc 2 P, A.average (A.sourceBeforeMean u P completionSwitch p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2)) + A.average (divProduct ij.1 ij.2) +
          A.labelAdv (u.B ij.1) (u.B ij.2))) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2))) ≤
        K * L * (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2)) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.average (divProduct ij.1 ij.2)) ≤ K * L * (s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2)) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
      U n (A.labelAdv (u.B ij.1) (u.B ij.2)) ≤
        K * L * (s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) →
    (∀ n, n + 1 ≤ H → U n residual ≤ K * freq ^ hierarchyMeanExponent 2) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, s.mean n p ≤ K * L * s.meanSource (n + 1) p) →
    (∀ p ∈ Finset.Icc 2 P, A.average (A.relayAtLevel u completionSwitch p) = 0) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, W n (A.relayAtLevel u completionSwitch p) ≤
      K * L * (freq ^ (-1 : ℝ) * (s'.osc (n + 1) (p - 1) + s.oscSource (n + 1) (p - 1)))) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
      W n (A.labelProduct u ij - A.average (A.labelProduct u ij)) ≤
        K * L * (s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2)) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 1 p,
      W n (A.completionPhaseProduct u ij - A.average (A.completionPhaseProduct u ij)) ≤
        (K * L * freq ^ (3 / 2 : ℝ)) * (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2)) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 1 p,
      W n (A.meanPhaseProduct u ij) ≤
        (K * L * freq ^ (3 / 2 : ℝ)) * (s.mean n ij.1 * s.Y (n + 1) ij.2)) →
    (∀ n ≤ H, ∀ p ∈ Finset.Icc 2 P, s.osc n p ≤ K * L * s.oscSource n p) →
    (∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 1 P,
      W n (u.C p) ≤ K * L * freq ^ (-1 : ℝ) * s'.osc (n + 1) p) →
    (∀ n ≤ H, W n (u.V 1) ≤ osc₁ n) →
    HierarchyNormRecurrence s' freq L K P H := by
  intro s s' hle hseed hB1 hC0 hexact hYY hdivY hBB hres hmeanSolve hrelayMean hrelay hslow
    hfast hmeanPhase hoscSolve hcomplete hV1
  have hKL0 : ∀ n, 0 ≤ s.osc n 1 := fun n => (s.nonneg n 1).2.2.1
  refine ⟨?_, ?_, ?_, hmeanSolve, ?_, ?_, hcomplete, ?_, ?_⟩
  · intro n hn
    change osc₁ n ≤ _
    exact hseed n hn
  · intro n
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [s', s, measuredLevels', HierarchyMeasuredLevels.ofProfiles]
    · simp [s', s, measuredLevels', HierarchyMeasuredLevels.ofProfiles]
    · change U n (u.B 1) = 0
      rw [hB1, map_zero]
    · change W n (u.C 0) = 0
      rw [hC0, map_zero]
  · intro n hn p hp
    have h := HierarchyMeasuredLevels.ofProfiles_meanForcing_of_average_eq A u hp n
      completionSwitch residual hf U W pW divProduct (hexact p hp) (K := K) (L := L)
      (hYY n hn p hp) (hdivY n hn p hp) (hBB n hn p hp) (fun _ => hres n hn)
    refine h.trans ?_
    change _ ≤ K * L * (∑ ij ∈ hierarchyLevelPairs P 0 p,
        (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2 + s'.osc (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) +
      (if p = 2 then K * freq ^ hierarchyMeanExponent 2 else 0)
    refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij _ => ?_) hKL) le_rfl
    exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (measuredLevels'_osc_le s osc₁ h₁ hle _ _) (s.nonneg _ _).2.2.2.2.2.1)) le_rfl
  · intro n hn p hp
    exact oscForcing_gen A u hp n completionSwitch residual hf U W (fun j => pW j)
      (fun j => apply_nonneg (pW j)) (hrelayMean p hp) _ (hrelay n hn p hp) (hslow n hn p hp)
      (hfast n hn p hp) (hmeanPhase n hn p hp)
  · intro n hn p hp
    have hp1 : p ≠ 1 := by have := (Finset.mem_Icc.mp hp).1; omega
    rw [measuredLevels'_osc_of_ne s osc₁ h₁ hp1]
    exact hoscSolve n hn p hp
  · intro n hn p hp
    change W n (u.V p + u.C (p - 1)) ≤ s'.osc n p + W n (u.C (p - 1))
    refine (map_add_le_add (W n) _ _).trans (add_le_add ?_ le_rfl)
    by_cases hp1 : p = 1
    · subst hp1
      change W n (u.V 1) ≤ osc₁ n
      exact hV1 n hn
    · rw [measuredLevels'_osc_of_ne s osc₁ h₁ hp1]
      change W n (u.V p) ≤ W n (u.V p) + freq * pW n (u.p p)
      exact le_add_of_nonneg_right (mul_nonneg hf (apply_nonneg _ _))
  · intro n hn p hp
    exact le_rfl

end Algebra

end

end TorusEuler.Paper.S5b
