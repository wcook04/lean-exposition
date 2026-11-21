import TorusEuler.HierarchyLevelBounds
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-! Summation and the depth remainder of the measured finite hierarchy. -/

namespace TorusEuler

section ProfileSums

variable {E Q : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]

private theorem hierarchySeminorm_sum_le {ι : Type*} (N : Seminorm ℝ E)
    (s : Finset ι) (f : ι → E) : N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
  exact norm_sum_le s f

/-- The same bound for the exact remainder in a finite-order profile seminorm. -/
theorem hierarchySeminorm_remainder_le (A : HierarchyOperators E Q)
    (u : HierarchyProfiles E Q) (P : ℕ) (N : Seminorm ℝ E)
    {freq loss C : ℝ} (hf : 1 ≤ freq) (hL : 0 ≤ loss) (hC : 0 ≤ C)
    (hsmall : loss * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hlinear : N (A.material (u.C P) + A.labelGrad (u.p P)) ≤
      C * (loss * freq ^ hierarchyCompletionExponent P))
    (hslow : ∀ ij ∈ hierarchyTailPairs P 0, N (A.labelProduct u ij) ≤
      C * (loss * freq ^ (hierarchyOscExponent ij.1 + hierarchyOscExponent ij.2)))
    (hfastCompletion : ∀ ij ∈ hierarchyTailPairs P 1, N (A.completionPhaseProduct u ij) ≤ C *
      (loss * freq ^ (3 / 2 + hierarchyCompletionExponent (ij.1 - 1) + hierarchyOscExponent ij.2)))
    (hfastMean : ∀ ij ∈ hierarchyTailPairs P 1, N (A.meanPhaseProduct u ij) ≤ C *
      (loss * freq ^ (3 / 2 + hierarchyInductiveMeanExponent ij.1 + hierarchyOscExponent ij.2))) :
    N (A.remainder u P) ≤ C *
      (1 + ((hierarchyTailPairs P 0).card : ℝ) + 2 * ((hierarchyTailPairs P 1).card : ℝ)) *
        freq ^ hierarchyOscExponent (P + 1) := by
  let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
  exact norm_hierarchy_tail_model P (A.material (u.C P) + A.labelGrad (u.p P))
    (A.labelProduct u) (A.completionPhaseProduct u) (A.meanPhaseProduct u)
    hf hL hC hsmall hlinear hslow hfastCompletion hfastMean

set_option maxHeartbeats 1000000 in
/-- The finite hierarchy bounds give the total oscillation, the corrections
beyond the primary velocity, and the total mean at their respective rates. -/
theorem hierarchySeminorm_velocity_sums (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    {P : ℕ} (hP : 1 ≤ P) (n : ℕ) (v w : ℕ → Seminorm ℝ E) (q : ℕ → Q → ℝ)
    (hq : ∀ m p, 0 ≤ q m p) (completionSwitch residual : E) {freq loss C : ℝ}
    (hf : 1 ≤ freq) (hL : 1 ≤ loss) (hC : 0 ≤ C)
    (hlevels : ∀ p ∈ Finset.Icc 1 P,
      HierarchyLevelBound (HierarchyMeasuredLevels.ofProfiles A u P completionSwitch residual freq
        (zero_le_one.trans hf) (fun m => v m) (fun m => w m) q
        (fun m => apply_nonneg (v m)) (fun m => apply_nonneg (w m)) hq) freq loss C n p) :
    let B := ((Finset.Icc 1 P).card : ℝ)
    let osc := ∑ p ∈ Finset.Icc 1 P, (u.V p + u.C p)
    w n osc ≤ 2 * B * C * loss ^ 2 * freq ^ (-5 / 4 : ℝ) ∧
    w n (osc - u.V 1) ≤ 2 * B * C * loss ^ 2 * freq ^ (-23 / 12 : ℝ) ∧
    v n (∑ p ∈ Finset.Icc 2 P, u.B p) ≤ B * C * loss ^ 6 * freq ^ (-5 / 2 : ℝ) := by
  classical
  intro B osc
  let S := Finset.Icc 1 P
  have hL₀ : 0 ≤ loss := zero_le_one.trans hL
  have hL₂ : loss ≤ loss ^ 2 := by nlinarith [mul_nonneg hL₀ (sub_nonneg.mpr hL)]
  have hV (p : ℕ) (hp : p ∈ S) : w n (u.V p) ≤ C * loss ^ 2 * freq ^ hierarchyOscExponent p := by
    have h := (hlevels p hp).osc
    change w n (u.V p) + freq * q n (u.p p) ≤ _ at h
    exact (le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hf) (hq n (u.p p)))).trans
      (h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL₂ hC) (by positivity)))
  have hC' (p : ℕ) (hp : p ∈ S) : w n (u.C p) ≤ C * loss ^ 2 * freq ^ hierarchyCompletionExponent p :=
    (hlevels p hp).completion
  have hpow {e e' : ℝ} (h : e ≤ e') : C * loss ^ 2 * freq ^ e ≤ C * loss ^ 2 * freq ^ e' :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hf h) (by positivity)
  have hV₁ (p : ℕ) (hp : p ∈ S) : w n (u.V p) ≤ C * loss ^ 2 * freq ^ (-5 / 4 : ℝ) := by
    have h := hierarchyOscExponent_antitone (Finset.mem_Icc.mp hp).1
    exact (hV p hp).trans (hpow (h.trans_eq (by norm_num [hierarchyOscExponent])))
  have hC₁ (p : ℕ) (hp : p ∈ S) : w n (u.C p) ≤ C * loss ^ 2 * freq ^ (-23 / 12 : ℝ) := by
    have h := hierarchyOscExponent_antitone (Finset.mem_Icc.mp hp).1
    norm_num [hierarchyOscExponent] at h
    exact (hC' p hp).trans (hpow (by unfold hierarchyCompletionExponent hierarchyOscExponent; linarith))
  have hC₀ (p : ℕ) (hp : p ∈ S) : w n (u.C p) ≤ C * loss ^ 2 * freq ^ (-5 / 4 : ℝ) :=
    (hC₁ p hp).trans (hpow (by norm_num))
  have h2 (p : ℕ) (hp : p ∈ S) (hp2 : 2 ≤ p) : w n (u.V p) ≤ C * loss ^ 2 * freq ^ (-23 / 12 : ℝ) := by
    have h := hierarchyOscExponent_antitone hp2
    exact (hV p hp).trans (hpow (h.trans_eq (by norm_num [hierarchyOscExponent])))
  have hosc : osc = ∑ p ∈ S, (u.V p + u.C p) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hosc]
    calc
      _ ≤ ∑ p ∈ S, w n (u.V p + u.C p) := hierarchySeminorm_sum_le (w n) S _
      _ ≤ ∑ _p ∈ S, (2 * (C * loss ^ 2 * freq ^ (-5 / 4 : ℝ))) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [two_mul]
        exact (map_add_le_add (w n) _ _).trans (add_le_add (hV₁ p hp) (hC₀ p hp))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; change _ = 2 * (S.card : ℝ) * _ * _ * _; ring
  · have hone : 1 ∈ S := Finset.mem_Icc.mpr ⟨le_rfl, hP⟩
    have hdiff : osc - u.V 1 = ∑ p ∈ S, ((if p = 1 then 0 else u.V p) + u.C p) := by
      rw [hosc, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [← Finset.sum_erase_add S u.V hone]
      have hs : (∑ p ∈ S, if p = 1 then 0 else u.V p) = ∑ p ∈ S.erase 1, u.V p := by
        rw [← Finset.sum_erase_add S (fun p => if p = 1 then 0 else u.V p) hone]
        simp only [ite_true, add_zero]
        exact Finset.sum_congr rfl (fun p hp => ite_eq_right (Finset.mem_erase.mp hp).1)
      rw [hs]
      abel
    rw [hdiff]
    calc
      _ ≤ ∑ p ∈ S, w n ((if p = 1 then 0 else u.V p) + u.C p) := hierarchySeminorm_sum_le (w n) S _
      _ ≤ ∑ _p ∈ S, (2 * (C * loss ^ 2 * freq ^ (-23 / 12 : ℝ))) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [two_mul]
        refine (map_add_le_add (w n) _ _).trans (add_le_add ?_ (hC₁ p hp))
        by_cases hep : p = 1
        · rw [ite_eq_left hep, map_zero]
          positivity
        · rw [ite_eq_right hep]
          exact h2 p hp (by have := (Finset.mem_Icc.mp hp).1; omega)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; change _ = 2 * (S.card : ℝ) * _ * _ * _; ring
  · have hsub : Finset.Icc 2 P ⊆ S := fun p hp =>
      Finset.mem_Icc.mpr ⟨(by omega : 1 ≤ 2).trans (Finset.mem_Icc.mp hp).1, (Finset.mem_Icc.mp hp).2⟩
    calc
      _ ≤ ∑ p ∈ Finset.Icc 2 P, v n (u.B p) := hierarchySeminorm_sum_le (v n) _ _
      _ ≤ ∑ _p ∈ Finset.Icc 2 P, (C * loss ^ 6 * freq ^ (-5 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have h := (hlevels p (hsub hp)).meanStrong
        refine h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hf ?_) (by positivity))
        unfold hierarchyMeanExponent
        have hc : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
        linarith
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hn : ((Finset.Icc 2 P).card : ℝ) ≤ B := by
          change ((Finset.Icc 2 P).card : ℝ) ≤ (S.card : ℝ)
          exact_mod_cast Finset.card_le_card hsub
        exact (mul_le_mul_of_nonneg_right hn (by positivity)).trans_eq (by ring)

end ProfileSums

end TorusEuler
