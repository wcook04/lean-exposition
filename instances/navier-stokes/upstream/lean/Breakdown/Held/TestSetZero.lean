import Mathlib
import Breakdown.Held.Statements

open Matrix

noncomputable section

namespace Breakdown.Held

namespace Internal

theorem convexOn_sum_sq {k : ℕ} (t : Finset (Fin k)) (s : Fin k → ℝ) :
    ConvexOn ℝ Set.univ (fun p : Fin k → ℝ => ∑ j ∈ t, (s j * p j) ^ 2) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_univ (𝕜 := ℝ) (E := Fin k → ℝ))
  | insert a t ha ih =>
    have h1 : ConvexOn ℝ Set.univ (fun p : Fin k → ℝ => (s a * p a) ^ 2) := by
      have := (even_two.convexOn_pow (𝕜 := ℝ)).comp_linearMap
        (s a • LinearMap.proj a : (Fin k → ℝ) →ₗ[ℝ] ℝ)
      simpa [Function.comp_def] using this
    have e : (fun p : Fin k → ℝ => ∑ j ∈ insert a t, (s j * p j) ^ 2) =
        (fun p => (s a * p a) ^ 2) + (fun p => ∑ j ∈ t, (s j * p j) ^ 2) := by
      funext p
      simp [Finset.sum_insert ha]
    rw [e]
    exact h1.add ih

theorem convex_testSet {k : ℕ} (Ja : Finset (Fin k)) (rad s : Fin k → ℝ) (εs : ℝ) :
    Convex ℝ (testSet Ja rad s εs) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun j hj => ?_, ?_⟩
  · have h1 := hx.1 j hj
    have h2 := hy.1 j hj
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * x j + b * y j| ≤ |a * x j| + |b * y j| := abs_add_le _ _
      _ = a * |x j| + b * |y j| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * rad j + b * rad j := by gcongr
      _ = rad j := by rw [← add_mul, hab, one_mul]
  · have hc := (convexOn_sum_sq Jaᶜ s).convex_le (εs ^ 2)
    exact (hc ⟨Set.mem_univ x, hx.2⟩ ⟨Set.mem_univ y, hy.2⟩ ha hb hab).2

theorem isClosed_testSet {k : ℕ} (Ja : Finset (Fin k)) (rad s : Fin k → ℝ) (εs : ℝ) :
    IsClosed (testSet Ja rad s εs) := by
  have e : testSet Ja rad s εs = (⋂ j ∈ Ja, {p : Fin k → ℝ | |p j| ≤ rad j}) ∩
      {p | ∑ j ∈ Jaᶜ, (s j * p j) ^ 2 ≤ εs ^ 2} := by
    ext p
    simp [testSet]
  rw [e]
  refine IsClosed.inter (isClosed_biInter fun j _ => isClosed_le ?_ continuous_const)
    (isClosed_le ?_ continuous_const)
  · exact continuous_abs.comp (continuous_apply j)
  · exact continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (continuous_apply j)).pow 2

theorem isBounded_testSet {k : ℕ} (Ja : Finset (Fin k)) (rad s : Fin k → ℝ) (εs : ℝ)
    (hs : ∀ j, s j ≠ 0) (hε : 0 ≤ εs) : Bornology.IsBounded (testSet Ja rad s εs) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨∑ j, (|rad j| + εs / |s j|), fun p hp => ?_⟩
  have hnn : ∀ i, 0 ≤ |rad i| + εs / |s i| := fun i => by positivity
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hnn i)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  have hj : |p j| ≤ |rad j| + εs / |s j| := by
    by_cases hJ : j ∈ Ja
    · have h1 := hp.1 j hJ
      have h2 : 0 ≤ εs / |s j| := by positivity
      linarith [le_abs_self (rad j)]
    · have hsq : (s j * p j) ^ 2 ≤ εs ^ 2 :=
        le_trans (Finset.single_le_sum (f := fun i => (s i * p i) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_compl.2 hJ)) hp.2
      have h1 : |s j * p j| ≤ εs := by
        have := sq_le_sq.1 hsq
        rwa [abs_of_nonneg hε] at this
      have hpos : 0 < |s j| := abs_pos.2 (hs j)
      have h2 : |p j| ≤ εs / |s j| := by
        rw [le_div_iff₀ hpos, mul_comm, ← abs_mul]
        exact h1
      linarith [abs_nonneg (rad j)]
  exact le_trans hj (Finset.single_le_sum (f := fun i => |rad i| + εs / |s i|)
    (fun i _ => hnn i) (Finset.mem_univ j))

theorem zero_mem_testSet {k : ℕ} (Ja : Finset (Fin k)) (rad s : Fin k → ℝ) (εs : ℝ)
    (hrad : ∀ j ∈ Ja, 0 ≤ rad j) : (0 : Fin k → ℝ) ∈ testSet Ja rad s εs := by
  refine ⟨fun j hj => ?_, ?_⟩
  · simpa using hrad j hj
  · simp [sq_nonneg]

end Internal

open Internal

theorem testSetZero_of (h : ConvexCompactFixedPointStatement) : TestSetZeroStatement := by
  intro k Ja rad s εs U Φ hrad hε hs hU hΦ hA hS
  let T : (Fin k → ℝ) → Fin k → ℝ := fun p j => p j - (Uᵀ *ᵥ Φ p) j / s j
  have hT : ContinuousOn T (testSet Ja rad s εs) := by
    have hM : ContinuousOn (fun p => Uᵀ *ᵥ Φ p) (testSet Ja rad s εs) :=
      (Matrix.mulVecLin Uᵀ).continuous_of_finiteDimensional.comp_continuousOn hΦ
    refine continuousOn_pi.2 fun j => ?_
    exact (continuous_apply j).continuousOn.sub
      (((continuous_apply j).comp_continuousOn hM).div_const _)
  have hmaps : Set.MapsTo T (testSet Ja rad s εs) (testSet Ja rad s εs) := by
    intro p hp
    refine ⟨fun j hj => ?_, ?_⟩
    · have hsj := hs j
      have e : T p j = -(((Uᵀ *ᵥ Φ p) j - s j * p j) / s j) := by
        simp only [T]
        field_simp
        ring
      rw [e, abs_neg, abs_div, div_le_iff₀ (abs_pos.2 hsj)]
      linarith [hA p hp j hj]
    · have e : ∀ j, s j * T p j = -((Uᵀ *ᵥ Φ p) j - s j * p j) := fun j => by
        have hsj := hs j
        simp only [T]
        field_simp
        ring
      simp_rw [e, neg_sq]
      exact hS p hp
  obtain ⟨p, hp, hfix⟩ := h (testSet Ja rad s εs) (convex_testSet Ja rad s εs)
    (Metric.isCompact_of_isClosed_isBounded (isClosed_testSet Ja rad s εs)
      (isBounded_testSet Ja rad s εs hs hε))
    ⟨0, zero_mem_testSet Ja rad s εs hrad⟩ T hT hmaps
  refine ⟨p, hp, ?_⟩
  have hz : Uᵀ *ᵥ Φ p = 0 := by
    funext j
    have h1 := congrFun hfix j
    simp only [T] at h1
    have h2 : (Uᵀ *ᵥ Φ p) j / s j = 0 := by linarith
    rcases div_eq_zero_iff.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 (hs j)
  have hinj : Function.Injective (Uᵀ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_transpose U hU))
  exact hinj (by rw [hz, Matrix.mulVec_zero])

end Breakdown.Held
