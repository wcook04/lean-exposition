import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open ContinuousLinearMap Set

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The line joining the identity to the projected operator. -/
def freezingContinuationLine (S : E →L[ℝ] E) (s : ℝ) : E →L[ℝ] E :=
  (1 - s) • (1 : E →L[ℝ] E) + s • S

@[simp] theorem freezingContinuationLine_zero (S : E →L[ℝ] E) :
    freezingContinuationLine S 0 = 1 := by simp [freezingContinuationLine]

@[simp] theorem freezingContinuationLine_one (S : E →L[ℝ] E) :
    freezingContinuationLine S 1 = S := by simp [freezingContinuationLine]

theorem freezingContinuationLine_sub (S : E →L[ℝ] E) (s t : ℝ) :
    freezingContinuationLine S s - freezingContinuationLine S t = (s - t) • (S - 1) := by
  simp only [freezingContinuationLine, sub_smul, smul_sub, one_smul]
  abel

/-- On the fixed subspace of a projection, projecting the affine line commutes with forming it. -/
theorem freezingContinuationLine_project (P B : E →L[ℝ] E) (s : ℝ) {v : E} (hv : P v = v) :
    P (freezingContinuationLine B s v) = freezingContinuationLine (P * B) s v := by
  simp [freezingContinuationLine, hv]

private theorem norm_ringInverse_le_of_apriori {A : E →L[ℝ] E} {M : ℝ}
    (hA : IsUnit A) (hM : 0 ≤ M) (hbound : ∀ v, ‖v‖ ≤ M * ‖A v‖) :
    ‖Ring.inverse A‖ ≤ M := by
  apply opNorm_le_bound _ hM
  intro v
  have hright : A (Ring.inverse A v) = v :=
    DFunLike.congr_fun (Ring.mul_inverse_cancel A hA) v
  simpa only [hright] using hbound (Ring.inverse A v)

/-- The resolvent identity bounds changes in the inverse in operator norm. -/
theorem norm_ringInverse_sub_le {A B : E →L[ℝ] E} (hA : IsUnit A) (hB : IsUnit B) :
    ‖Ring.inverse A - Ring.inverse B‖ ≤ ‖Ring.inverse A‖ * ‖A - B‖ * ‖Ring.inverse B‖ := by
  rw [Ring.inverse_sub_inverse (iff_of_true hA hB), norm_sub_rev A B]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- The inverse of a continuous family is norm-continuous wherever its inverse norms are
uniformly bounded. -/
theorem continuousOn_ringInverse_of_uniform_bound {X : Type*} [TopologicalSpace X]
    {U : Set X} {A : X → E →L[ℝ] E} {M : ℝ} (hA : ContinuousOn A U)
    (hu : ∀ x ∈ U, IsUnit (A x)) (hM : ∀ x ∈ U, ‖Ring.inverse (A x)‖ ≤ M) :
    ContinuousOn (fun x => Ring.inverse (A x)) U := by
  let D := {B : E →L[ℝ] E | IsUnit B ∧ ‖Ring.inverse B‖ ≤ M}
  have hL : LipschitzOnWith ⟨M ^ 2, sq_nonneg M⟩ Ring.inverse D := by
    refine LipschitzOnWith.of_dist_le_mul (fun B hB C hC => ?_)
    obtain ⟨hBu, hBnorm⟩ := hB
    obtain ⟨hCu, hCnorm⟩ := hC
    have hM0 := (norm_nonneg _).trans hBnorm
    simp only [dist_eq_norm]
    change ‖Ring.inverse B - Ring.inverse C‖ ≤ M ^ 2 * ‖B - C‖
    calc
      _ ≤ ‖Ring.inverse B‖ * ‖B - C‖ * ‖Ring.inverse C‖ := norm_ringInverse_sub_le hBu hCu
      _ ≤ M * ‖B - C‖ * M := by gcongr
      _ = _ := by ring
  exact hL.continuousOn.comp hA (fun x hx => ⟨hu x hx, hM x hx⟩)

variable [CompleteSpace E]

private theorem isUnit_of_neumann_step {A B : E →L[ℝ] E} {M : ℝ}
    (hA : IsUnit A) (hM : 0 ≤ M) (hbound : ∀ v, ‖v‖ ≤ M * ‖A v‖)
    (hstep : M * ‖A - B‖ < 1) : IsUnit B := by
  have hsmall : ‖Ring.inverse A * (A - B)‖ < 1 := calc
    ‖Ring.inverse A * (A - B)‖ ≤ ‖Ring.inverse A‖ * ‖A - B‖ := norm_mul_le _ _
    _ ≤ M * ‖A - B‖ :=
      mul_le_mul_of_nonneg_right (norm_ringInverse_le_of_apriori hA hM hbound) (norm_nonneg _)
    _ < 1 := hstep
  have hneumann : IsUnit (1 - Ring.inverse A * (A - B)) := (Units.oneSub _ hsmall).isUnit
  have heq : A * (1 - Ring.inverse A * (A - B)) = B := by
    rw [mul_sub, mul_one, ← mul_assoc, Ring.mul_inverse_cancel A hA, one_mul, sub_sub_self]
  exact heq ▸ hA.mul hneumann

/-- A subdivision satisfying the Neumann step bound reaches every parameter on the line. -/
theorem freezingContinuationLine_isUnit_of_subdivision (S : E →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, ‖v‖ ≤ M * ‖freezingContinuationLine S s v‖)
    {n : ℕ} (hn : M * ‖S - 1‖ < (n : ℝ)) {s : ℝ} (hs : s ∈ Icc 0 1) :
    IsUnit (freezingContinuationLine S s) := by
  have hnpos : 0 < (n : ℝ) := (mul_nonneg hM (norm_nonneg _)).trans_lt hn
  let t (k : ℕ) : ℝ := ((k : ℝ) / (n : ℝ)) * s
  have ht (k : ℕ) (hk : k ≤ n) : t k ∈ Icc (0 : ℝ) 1 := by
    have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    exact ⟨mul_nonneg (div_nonneg (Nat.cast_nonneg _) hnpos.le) hs.1,
      ((mul_le_mul_of_nonneg_right ((div_le_one hnpos).mpr hkn) hs.1).trans_eq
        (one_mul s)).trans hs.2⟩
  have hstep (k : ℕ) : M * ‖freezingContinuationLine S (t k) - freezingContinuationLine S (t (k + 1))‖ < 1 := by
    have hdelta : t k - t (k + 1) = -(s / (n : ℝ)) := by
      simp only [t, Nat.cast_add, Nat.cast_one]
      ring
    rw [freezingContinuationLine_sub, hdelta, norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hs.1 hnpos.le)]
    calc
      _ = (M * ‖S - 1‖ * s) / (n : ℝ) := by ring
      _ ≤ (M * ‖S - 1‖) / (n : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_of_le_one_right (mul_nonneg hM (norm_nonneg _)) hs.2) hnpos.le
      _ < 1 := (div_lt_one hnpos).mpr hn
  have hgrid (k : ℕ) (hk : k ≤ n) : IsUnit (freezingContinuationLine S (t k)) := by
    induction k with
    | zero => simpa only [t, Nat.cast_zero, zero_div, zero_mul, freezingContinuationLine_zero] using
        (isUnit_one : IsUnit (1 : E →L[ℝ] E))
    | succ k ih =>
        have hkn : k ≤ n := (Nat.le_succ k).trans hk
        exact isUnit_of_neumann_step (ih hkn) hM (hbound _ (ht k hkn)) (hstep k)
  simpa only [t, div_self hnpos.ne', one_mul] using hgrid n le_rfl

/-- The uniform a priori estimate propagates invertibility from zero along the whole line. -/
theorem freezingContinuationLine_isUnit (S : E →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, ‖v‖ ≤ M * ‖freezingContinuationLine S s v‖)
    {s : ℝ} (hs : s ∈ Icc 0 1) : IsUnit (freezingContinuationLine S s) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (M * ‖S - 1‖)
  exact freezingContinuationLine_isUnit_of_subdivision S hM hbound (n := n) hn hs

theorem norm_freezingContinuationLine_inverse_le (S : E →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, ‖v‖ ≤ M * ‖freezingContinuationLine S s v‖)
    {s : ℝ} (hs : s ∈ Icc 0 1) : ‖Ring.inverse (freezingContinuationLine S s)‖ ≤ M :=
  norm_ringInverse_le_of_apriori (freezingContinuationLine_isUnit S hM hbound hs) hM (hbound s hs)

theorem norm_freezingContinuationLine_inverse_sub_le (S : E →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, ‖v‖ ≤ M * ‖freezingContinuationLine S s v‖)
    {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    ‖Ring.inverse (freezingContinuationLine S s) - Ring.inverse (freezingContinuationLine S t)‖ ≤
      M ^ 2 * ‖S - 1‖ * |s - t| := by
  have hresolvent := norm_ringInverse_sub_le (freezingContinuationLine_isUnit S hM hbound hs)
    (freezingContinuationLine_isUnit S hM hbound ht)
  rw [freezingContinuationLine_sub, norm_smul, Real.norm_eq_abs] at hresolvent
  refine hresolvent.trans ?_
  calc
    _ ≤ M * (|s - t| * ‖S - 1‖) * M := by
      gcongr
      · exact norm_freezingContinuationLine_inverse_le S hM hbound hs
      · exact norm_freezingContinuationLine_inverse_le S hM hbound ht
    _ = _ := by ring

theorem freezingContinuationLine_inverse_continuousOn (S : E →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, ‖v‖ ≤ M * ‖freezingContinuationLine S s v‖) :
    ContinuousOn (fun s => Ring.inverse (freezingContinuationLine S s)) (Icc 0 1) := by
  apply continuousOn_ringInverse_of_uniform_bound (M := M)
  · unfold freezingContinuationLine
    fun_prop
  · exact fun _ hs => freezingContinuationLine_isUnit S hM hbound hs
  · exact fun _ hs => norm_freezingContinuationLine_inverse_le S hM hbound hs

/-- The terminal operator is a bounded equivalence with inverse norm at most the a priori constant. -/
theorem exists_freezingContinuationEquiv (S : E →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, ‖v‖ ≤ M * ‖freezingContinuationLine S s v‖) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = S ∧ ‖(e.symm : E →L[ℝ] E)‖ ≤ M := by
  have hone : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hS : IsUnit S := by simpa using freezingContinuationLine_isUnit S hM hbound hone
  obtain ⟨u, hu⟩ := hS
  refine ⟨ContinuousLinearEquiv.ofUnit u, hu, ?_⟩
  change ‖(↑(u⁻¹) : E →L[ℝ] E)‖ ≤ M
  rw [← Ring.inverse_unit, hu]
  simpa using norm_freezingContinuationLine_inverse_le S hM hbound hone

end TorusEuler
