import TorusEuler.TerminalProfileTimeDerivatives
import TorusEuler.HierarchyActualNorms
import Mathlib.Data.Nat.Choose.Cast

/-! The factorial time jet norms used in the terminal smoothness argument. -/

open Finset Finset.HasAntidiagonal

namespace TorusEuler

noncomputable section

/-- The coefficient multiplying the norm of the (i)-th time derivative. -/
def terminalTimeJetWeight (T : ℝ) (i : ℕ) : ℝ := T ^ i / i.factorial

@[simp] theorem terminalTimeJetWeight_zero (T : ℝ) : terminalTimeJetWeight T 0 = 1 := by
  simp [terminalTimeJetWeight]

theorem terminalTimeJetWeight_pos {T : ℝ} (hT : 0 < T) (i : ℕ) :
    0 < terminalTimeJetWeight T i :=
  div_pos (pow_pos hT i) (Nat.cast_pos.mpr (Nat.factorial_pos i))

theorem terminalTimeJetWeight_mul_choose (T : ℝ) {n i : ℕ} (hi : i ≤ n) :
    terminalTimeJetWeight T n * (n.choose i : ℝ) =
      terminalTimeJetWeight T i * terminalTimeJetWeight T (n - i) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hpow : T ^ n = T ^ i * T ^ (n - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  unfold terminalTimeJetWeight
  rw [Nat.cast_choose ℝ hi, hpow]
  field_simp

private theorem terminalTimeAntidiagonal_le (q : ℕ) {u v : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    (∑ n ∈ range (q + 1), ∑ p ∈ antidiagonal n, u p.1 * v p.2) ≤
      (∑ i ∈ range (q + 1), u i) * (∑ j ∈ range (q + 1), v j) := by
  let R := range (q + 1)
  let B := R ×ˢ R
  let order (p : ℕ × ℕ) := p.1 + p.2
  let term (p : ℕ × ℕ) := u p.1 * v p.2
  calc
    _ = ∑ n ∈ R, ∑ p ∈ B with order p = n, term p := by
      refine sum_congr rfl fun n hn => sum_congr ?_ (fun _ _ => rfl)
      ext p
      simp only [mem_antidiagonal, mem_filter, mem_product, mem_range, B, R, order]
      have hN : n < q + 1 := mem_range.mp hn
      omega
    _ = ∑ p ∈ B with order p ∈ R, term p := sum_fiberwise_eq_sum_filter B R order term
    _ ≤ ∑ p ∈ B, term p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => mul_nonneg (hu p.1) (hv p.2))
    _ = _ := by simp only [B, term, sum_product, ← mul_sum, ← sum_mul, R]

/-- The factorial weights turn the time Leibniz coefficients into an ordinary
convolution. Summing the lower triangle costs at most the product of the sums. -/
theorem terminalTimeConvolution_le {T : ℝ} (hT : 0 < T) (q : ℕ) {u v : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    (∑ n ∈ range (q + 1), terminalTimeJetWeight T n *
      (∑ i ∈ range (n + 1), (n.choose i : ℝ) * (u i * v (n - i)))) ≤
      (∑ i ∈ range (q + 1), terminalTimeJetWeight T i * u i) *
        (∑ j ∈ range (q + 1), terminalTimeJetWeight T j * v j) := by
  let a (i : ℕ) := terminalTimeJetWeight T i * u i
  let b (i : ℕ) := terminalTimeJetWeight T i * v i
  calc
    _ = ∑ n ∈ range (q + 1), ∑ p ∈ antidiagonal n, a p.1 * b p.2 := by
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine sum_congr rfl fun i hi => ?_
      have h : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [← mul_assoc, terminalTimeJetWeight_mul_choose T h]
      dsimp only [a, b]
      ring
    _ ≤ _ := terminalTimeAntidiagonal_le q
      (fun i => mul_nonneg (terminalTimeJetWeight_pos hT i).le (hu i))
      (fun i => mul_nonneg (terminalTimeJetWeight_pos hT i).le (hv i))

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3} {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Apply the spatial seminorm to each time derivative and then sum.
In particular an amplitude seminorm weights each differentiated slice by the
reciprocal amplitude, so the time derivative never acts on that weight. -/
def timeJetSeminorm (hT : 0 < T) (q : ℕ) (N : Seminorm ℝ (HierarchyTwistedProfile T k E)) :
    Seminorm ℝ (HierarchyTwistedProfile T k E) :=
  Seminorm.of (fun f => ∑ i ∈ range (q + 1), terminalTimeJetWeight T i * N (timeJet hT i f))
    (fun f g => by
      simp only [map_add, ← sum_add_distrib, ← mul_add]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (map_add_le_add N _ _)
        (terminalTimeJetWeight_pos hT i).le)
    (fun c f => by
      simp only [map_smul, map_smul_eq_mul, mul_sum]
      apply sum_congr rfl
      intro i _
      rw [mul_left_comm])

@[simp] theorem timeJetSeminorm_apply (hT : 0 < T) (q : ℕ)
    (N : Seminorm ℝ (HierarchyTwistedProfile T k E)) (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT q N f =
      ∑ i ∈ range (q + 1), terminalTimeJetWeight T i * N (timeJet hT i f) := rfl

@[simp] theorem timeJetSeminorm_zero (hT : 0 < T)
    (N : Seminorm ℝ (HierarchyTwistedProfile T k E)) (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT 0 N f = N f := by simp

theorem timeJetSeminorm_mono (hT : 0 < T) {p q : ℕ} (hpq : p ≤ q)
    (N : Seminorm ℝ (HierarchyTwistedProfile T k E)) (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT p N f ≤ timeJetSeminorm hT q N f := by
  simp only [timeJetSeminorm_apply]
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ hpq))
    (fun i _ _ => mul_nonneg (terminalTimeJetWeight_pos hT i).le (apply_nonneg N _))

theorem timeJetSeminorm_mono_seminorm (hT : 0 < T) (q : ℕ)
    {N M : Seminorm ℝ (HierarchyTwistedProfile T k E)} (hNM : N ≤ M)
    (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT q N f ≤ timeJetSeminorm hT q M f := by
  simp only [timeJetSeminorm_apply]
  exact sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (Seminorm.le_def.mp hNM _) (terminalTimeJetWeight_pos hT i).le

/-- Recovering a single time derivative costs precisely (i!T^{-i}). -/
theorem norm_timeJet_le (hT : 0 < T) {i q : ℕ} (hi : i ≤ q)
    (N : Seminorm ℝ (HierarchyTwistedProfile T k E)) (f : HierarchyTwistedProfile T k E) :
    N (timeJet hT i f) ≤ (i.factorial : ℝ) * T⁻¹ ^ i * timeJetSeminorm hT q N f := by
  have hterm : terminalTimeJetWeight T i * N (timeJet hT i f) ≤ timeJetSeminorm hT q N f := by
    rw [timeJetSeminorm_apply]
    exact single_le_sum (fun j _ => mul_nonneg (terminalTimeJetWeight_pos hT j).le
      (apply_nonneg N (timeJet hT j f))) (mem_range.mpr (Nat.lt_succ_of_le hi))
  have hw := terminalTimeJetWeight_pos hT i
  calc
    _ = (terminalTimeJetWeight T i)⁻¹ *
          (terminalTimeJetWeight T i * N (timeJet hT i f)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]
    _ ≤ (terminalTimeJetWeight T i)⁻¹ * timeJetSeminorm hT q N f :=
      mul_le_mul_of_nonneg_left hterm (inv_nonneg.mpr hw.le)
    _ = _ := by simp [terminalTimeJetWeight, div_eq_mul_inv, mul_comm]

/-- A jetwise bound for a linear operation gives the identical bound
in the factorial time norm. -/
theorem timeJetSeminorm_le_of_jetwise_le
    (hT : 0 < T) (q : ℕ) (N : Seminorm ℝ (HierarchyTwistedProfile T k E))
    (M : Seminorm ℝ (HierarchyTwistedProfile T k F))
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F) (C : ℝ)
    (h : ∀ i ≤ q, M (timeJet hT i g) ≤ C * N (timeJet hT i f)) :
    timeJetSeminorm hT q M g ≤ C * timeJetSeminorm hT q N f := by
  simp only [timeJetSeminorm_apply, mul_sum]
  exact sum_le_sum fun i hi => by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (h i (Nat.lt_succ_iff.mp (mem_range.mp hi)))
      (terminalTimeJetWeight_pos hT i).le

/-- The time extension of a spatial bilinear norm bound has the same
multiplicative cost once the pointwise jet convolution is available. -/
theorem timeJetSeminorm_bilinear_le_of_jetwise_le
    (hT : 0 < T) (q : ℕ) (NE : Seminorm ℝ (HierarchyTwistedProfile T k E))
    (NF : Seminorm ℝ (HierarchyTwistedProfile T k F))
    (NG : Seminorm ℝ (HierarchyTwistedProfile T k G))
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F)
    (v : HierarchyTwistedProfile T k G) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n ≤ q, NG (timeJet hT n v) ≤ C *
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
        (NE (timeJet hT i f) * NF (timeJet hT (n - i) g))) :
    timeJetSeminorm hT q NG v ≤ C * (timeJetSeminorm hT q NE f * timeJetSeminorm hT q NF g) := by
  simp only [timeJetSeminorm_apply]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left
    (terminalTimeConvolution_le hT q (fun i => apply_nonneg NE (timeJet hT i f))
      (fun i => apply_nonneg NF (timeJet hT i g))) hC)
  rw [mul_sum]
  exact sum_le_sum fun i hi => by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (h i (Nat.lt_succ_iff.mp (mem_range.mp hi)))
      (terminalTimeJetWeight_pos hT i).le

end HierarchyTwistedProfile

end

end TorusEuler
