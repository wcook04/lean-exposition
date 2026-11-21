import TorusEuler.ScalarBarriers
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set

namespace TorusEuler.ReferenceRiccati

noncomputable section

def x (ε τ : ℝ) : ℝ := ε * τ ^ 2 / 2

def s (ε τ : ℝ) : ℝ := (Real.sqrt (1 + x ε τ ^ 2))⁻¹

def damping (ε τ : ℝ) : ℝ := 2 * ε * τ * x ε τ * s ε τ ^ 2

def driving (ε τ : ℝ) : ℝ := s ε τ ^ 2 * (1 - ε * x ε τ)

def rhs (ε τ y : ℝ) : ℝ := driving ε τ - damping ε τ * y - y ^ 2

def deviationRhs (ε τ e : ℝ) : ℝ :=
  s ε τ * (-2 * e - e ^ 2 + ε * x ε τ * s ε τ ^ 2 / 2)

def referenceY (ε : ℝ) (e : ℝ → ℝ) (τ : ℝ) : ℝ :=
  s ε τ * (1 + e τ) - damping ε τ / 4

def deviation (ε : ℝ) (Y : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (Y τ + damping ε τ / 4) / s ε τ - 1

theorem x_nonneg {ε : ℝ} (hε : 0 ≤ ε) (τ : ℝ) : 0 ≤ x ε τ := by
  unfold x
  positivity

theorem s_pos (ε τ : ℝ) : 0 < s ε τ := by
  unfold s
  positivity

theorem s_sq_mul (ε τ : ℝ) : s ε τ ^ 2 * (1 + x ε τ ^ 2) = 1 := by
  have h : 0 < 1 + x ε τ ^ 2 := by positivity
  rw [s, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

@[simp] theorem s_zero (ε : ℝ) : s ε 0 = 1 := by
  simp [s, x]

@[simp] theorem damping_zero (ε : ℝ) : damping ε 0 = 0 := by
  simp [damping]

theorem s_le_one (ε τ : ℝ) : s ε τ ≤ 1 := by
  have hs := s_pos ε τ
  have hsq := s_sq_mul ε τ
  nlinarith [sq_nonneg (s ε τ - 1), sq_nonneg (x ε τ * s ε τ)]

theorem x_mul_s_sq_le_half (ε τ : ℝ) : x ε τ * s ε τ ^ 2 ≤ 1 / 2 := by
  have h := s_sq_mul ε τ
  nlinarith [sq_nonneg (x ε τ * s ε τ - s ε τ)]

theorem forcing_bounds {ε : ℝ} (hε : 0 ≤ ε) (τ : ℝ) :
    0 ≤ ε * x ε τ * s ε τ ^ 2 / 2 ∧ ε * x ε τ * s ε τ ^ 2 / 2 ≤ ε / 4 := by
  have hx := x_nonneg hε τ
  constructor
  · positivity
  · have h := mul_le_mul_of_nonneg_left (x_mul_s_sq_le_half ε τ) hε
    nlinarith

theorem hasDerivAt_x (ε τ : ℝ) : HasDerivAt (x ε) (ε * τ) τ := by
  unfold x
  have h : HasDerivAt (fun u : ℝ => u ^ 2) (2 * τ) τ := by
    simpa using hasDerivAt_pow 2 τ
  exact ((h.const_mul ε).div_const 2).congr_deriv (by ring)

private theorem hasDerivAt_s_expanded (ε τ : ℝ) :
    HasDerivAt (s ε) (-(ε * τ * x ε τ * s ε τ ^ 3)) τ := by
  have h : 0 < 1 + x ε τ ^ 2 := by positivity
  have hS := Real.sqrt_pos.2 h
  have h₁ : HasDerivAt (fun u => 1 + x ε u ^ 2)
      (↑(2 : ℕ) * x ε τ ^ (2 - 1) * (ε * τ)) τ :=
    ((hasDerivAt_x ε τ).fun_pow 2).const_add 1
  refine ((h₁.sqrt h.ne').fun_inv hS.ne').congr_deriv ?_
  unfold s
  field_simp
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- The logarithmic derivative of the clock factor is minus half the damping. -/
theorem hasDerivAt_s (ε τ : ℝ) :
    HasDerivAt (s ε) (-(damping ε τ / 2 * s ε τ)) τ :=
  (hasDerivAt_s_expanded ε τ).congr_deriv (by unfold damping; ring)

private theorem hasDerivAt_damping_quarter (ε τ : ℝ) :
    HasDerivAt (fun u => damping ε u / 4)
      (3 / 2 * ε * x ε τ * s ε τ ^ 2 - 2 * ε * x ε τ ^ 3 * s ε τ ^ 4) τ := by
  have heq : (fun u => damping ε u / 4) = fun u => ε * u * x ε u * s ε u ^ 2 / 2 := by
    funext u
    unfold damping
    ring
  rw [heq]
  have h := ((((hasDerivAt_id τ).const_mul ε).mul (hasDerivAt_x ε τ)).mul
    ((hasDerivAt_s_expanded ε τ).fun_pow 2)).div_const 2
  refine h.congr_deriv ?_
  simp only [id, Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, x]
  ring

theorem referenceY_deviation (ε : ℝ) (Y : ℝ → ℝ) : referenceY ε (deviation ε Y) = Y := by
  funext τ
  unfold referenceY deviation
  field_simp [(s_pos ε τ).ne']
  ring

theorem deviation_referenceY (ε : ℝ) (e : ℝ → ℝ) : deviation ε (referenceY ε e) = e := by
  funext τ
  unfold deviation referenceY
  field_simp [(s_pos ε τ).ne']
  ring

theorem referenceY_zero {ε : ℝ} {e : ℝ → ℝ} (h₀ : e 0 = 0) : referenceY ε e 0 = 1 := by
  simp [referenceY, h₀]

theorem deviation_zero {ε : ℝ} {Y : ℝ → ℝ} (h₀ : Y 0 = 1) : deviation ε Y 0 = 0 := by
  simp [deviation, h₀]

/-- Substitution into (2.7) for any path satisfying the deviation equation. -/
theorem hasDerivWithinAt_referenceY {ε τ : ℝ} {D : Set ℝ} {e : ℝ → ℝ}
    (he : HasDerivWithinAt e (deviationRhs ε τ (e τ)) D τ) :
    HasDerivWithinAt (referenceY ε e) (rhs ε τ (referenceY ε e τ)) D τ := by
  have hs := (hasDerivAt_s_expanded ε τ).hasDerivWithinAt (s := D)
  have hd := (hasDerivAt_damping_quarter ε τ).hasDerivWithinAt (s := D)
  refine ((hs.mul (he.const_add 1)).sub hd).congr_deriv ?_
  unfold rhs referenceY deviationRhs damping driving
  have hrel := s_sq_mul ε τ
  simp only [x] at hrel ⊢
  linear_combination (ε ^ 2 * τ ^ 2 * s ε τ ^ 2 / 4) * hrel

/-- The Riccati equation in (2.7) implies the deviation equation of Lemma 2.4. -/
theorem hasDerivWithinAt_deviation {ε τ : ℝ} {D : Set ℝ} {Y : ℝ → ℝ}
    (hY : HasDerivWithinAt Y (rhs ε τ (Y τ)) D τ) :
    HasDerivWithinAt (deviation ε Y) (deviationRhs ε τ (deviation ε Y τ)) D τ := by
  have hs := (s_pos ε τ).ne'
  have hrel := s_sq_mul ε τ
  have h := ((hY.add (hasDerivAt_damping_quarter ε τ).hasDerivWithinAt).div
    (hasDerivAt_s_expanded ε τ).hasDerivWithinAt hs).sub_const 1
  unfold deviation
  refine h.congr_deriv ?_
  simp only [Pi.add_apply]
  set scale := s ε τ with hscale
  set clock := x ε τ with hclock
  set B := Y τ + damping ε τ / 4 with hB
  have hB' : B = Y τ + ε * τ * clock * scale ^ 2 / 2 := by
    rw [hB, damping]
    ring
  have hnum : (rhs ε τ (Y τ) +
      (3 / 2 * ε * clock * scale ^ 2 - 2 * ε * clock ^ 3 * scale ^ 4)) * scale -
      B * -(ε * τ * clock * scale ^ 3) =
        -2 * (B - scale) * scale ^ 2 - (B - scale) ^ 2 * scale + ε * clock * scale ^ 5 / 2 := by
    rw [hB']
    unfold rhs driving damping
    rw [← hscale, ← hclock]
    simp only [hclock, x] at hrel ⊢
    linear_combination (-(ε ^ 2 * scale ^ 3 * τ ^ 2 / 4)) * hrel
  rw [hnum]
  unfold deviationRhs
  rw [← hscale, ← hclock]
  field_simp

private theorem hasDerivWithinAt_right {f : ℝ → ℝ} {d t a b : ℝ}
    (ht : t ∈ Ico a b) (hd : HasDerivWithinAt f d (Icc a b) t) :
    HasDerivWithinAt f d (Ici t) t := by
  apply (hd.mono (Icc_subset_Icc_left ht.1)).mono_of_mem_nhdsWithin
  rw [← nhdsWithin_Icc_eq_nhdsGE ht.2]
  exact self_mem_nhdsWithin

/-- The deviation equation preserves the interval from zero to epsilon over eight. -/
theorem deviation_bounds {ε T : ℝ} (hε : 0 < ε) {e : ℝ → ℝ} (h₀ : e 0 = 0)
    (he : ∀ τ ∈ Icc 0 T, HasDerivWithinAt e (deviationRhs ε τ (e τ)) (Icc 0 T) τ) :
    ∀ τ ∈ Icc 0 T, 0 ≤ e τ ∧ e τ ≤ ε / 8 := by
  have hec : ContinuousOn e (Icc 0 T) := fun τ hτ => (he τ hτ).continuousWithinAt
  have her : ∀ τ ∈ Ico 0 T, HasDerivWithinAt e (deviationRhs ε τ (e τ)) (Ici τ) τ :=
    fun τ hτ => hasDerivWithinAt_right hτ (he τ ⟨hτ.1, hτ.2.le⟩)
  intro τ hτ
  constructor
  · by_contra! hneg
    let δ := min 1 (-(e τ) / 2)
    have hδ : 0 < δ := lt_min one_pos (by linarith)
    have hδ₁ : δ ≤ 1 := min_le_left _ _
    have hδe : δ ≤ -(e τ) / 2 := min_le_right _ _
    have hcomp := image_le_of_deriv_right_lt_deriv_boundary
      (f := fun t => -e t) (f' := fun t => -deviationRhs ε t (e t)) (B := fun _ => δ)
      hec.neg (fun t ht => (her t ht).neg) (by rw [h₀, neg_zero]; exact hδ.le)
      (fun t => hasDerivAt_const t δ) ?_ hτ
    · linarith
    · intro t _ htEq
      have heq : e t = -δ := by linarith
      rw [heq]
      have hforce := (forcing_bounds hε.le t).1
      have hsign : 0 < -2 * -δ - (-δ) ^ 2 + ε * x ε t * s ε t ^ 2 / 2 := by
        nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ₁)]
      exact neg_neg_of_pos (mul_pos (s_pos ε t) hsign)
  · refine image_le_of_deriv_right_lt_deriv_boundary (B := fun _ => ε / 8)
      hec her (by rw [h₀]; positivity) (fun t => hasDerivAt_const t _) ?_ hτ
    intro t _ htEq
    rw [htEq]
    have hforce := (forcing_bounds hε.le t).2
    apply mul_neg_of_pos_of_neg (s_pos ε t)
    nlinarith [sq_pos_of_pos hε]

theorem riccati_deviation_bounds {ε T : ℝ} (hε : 0 < ε)
    {Y : ℝ → ℝ} (h₀ : Y 0 = 1)
    (hY : ∀ τ ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Icc 0 T) τ) :
    ∀ τ ∈ Icc 0 T, 0 ≤ deviation ε Y τ ∧ deviation ε Y τ ≤ ε / 8 :=
  deviation_bounds hε (deviation_zero h₀) (fun τ hτ => hasDerivWithinAt_deviation (hY τ hτ))

theorem riccati_deviation_bounds_Ici {ε : ℝ} (hε : 0 < ε)
    {Y : ℝ → ℝ} (h₀ : Y 0 = 1)
    (hY : ∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) :
    MapsTo (deviation ε Y) (Ici 0) (Icc 0 (ε / 8)) := by
  intro τ hτ
  exact riccati_deviation_bounds hε h₀
    (fun t ht => (hY t ht.1).mono Icc_subset_Ici_self) τ ⟨hτ, le_rfl⟩

theorem x_mul_s_lt_one (ε τ : ℝ) : x ε τ * s ε τ < 1 := by
  have hs := s_pos ε τ
  have hsq : (x ε τ * s ε τ) ^ 2 + s ε τ ^ 2 = 1 := by
    linear_combination s_sq_mul ε τ
  nlinarith [sq_pos_of_pos hs, sq_nonneg (x ε τ * s ε τ - 1)]

private theorem referenceY_eq (ε τ : ℝ) (e : ℝ → ℝ) :
    referenceY ε e τ = s ε τ * (1 + e τ - ε * τ * (x ε τ * s ε τ) / 2) := by
  unfold referenceY damping
  ring

/-- The reference solution is positive through the time at which epsilon times time is two. -/
theorem referenceY_pos {ε τ : ℝ} (hε : 0 ≤ ε) (h₂ : ε * τ ≤ 2)
    {e : ℝ → ℝ} (he : 0 ≤ e τ) : 0 < referenceY ε e τ := by
  have hprod : ε * τ * (x ε τ * s ε τ) < 2 := by
    calc
      _ ≤ 2 * (x ε τ * s ε τ) :=
        mul_le_mul_of_nonneg_right h₂ (mul_nonneg (x_nonneg hε τ) (s_pos ε τ).le)
      _ < 2 := by linarith [x_mul_s_lt_one ε τ]
  rw [referenceY_eq]
  exact mul_pos (s_pos ε τ) (by linarith)

/-- The reference solution is negative at the time at which epsilon times time is three. -/
theorem referenceY_neg_at_three {ε τ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (h₃ : ε * τ = 3) {e : ℝ → ℝ} (he : e τ ≤ ε / 8) : referenceY ε e τ < 0 := by
  have hx₀ := x_nonneg hε.le τ
  have hx : 9 / 2 ≤ x ε τ := by
    have h := congrArg (fun v : ℝ => v ^ 2) h₃
    have hmul : ε * x ε τ ≤ x ε τ := by nlinarith [mul_nonneg (sub_nonneg.mpr hε₁) hx₀]
    unfold x at hmul ⊢
    nlinarith
  have hxs : 3 / 4 < x ε τ * s ε τ := by
    have hs := s_pos ε τ
    have hsq : (x ε τ * s ε τ) ^ 2 + s ε τ ^ 2 = 1 := by
      linear_combination s_sq_mul ε τ
    have hp : 4 * s ε τ ≤ x ε τ * s ε τ := by
      exact mul_le_mul_of_nonneg_right (by linarith) hs.le
    by_contra! hc
    have hsp : s ε τ ≤ 3 / 16 := by linarith
    have hn : 0 ≤ x ε τ * s ε τ := mul_nonneg hx₀ hs.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hn, mul_nonneg (sub_nonneg.mpr hsp) hs.le]
  rw [referenceY_eq, h₃]
  exact mul_neg_of_pos_of_neg (s_pos ε τ) (by linarith)

private theorem continuous_uncurry_deviationRhs (ε : ℝ) :
    Continuous (Function.uncurry (deviationRhs ε)) := by
  have hs : Continuous (s ε) :=
    continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_s ε τ).continuousAt
  have hx : Continuous (x ε) :=
    continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_x ε τ).continuousAt
  unfold Function.uncurry deviationRhs
  fun_prop

private theorem deviationRhs_lipschitzOnWith {ε : ℝ} (hε₁ : ε ≤ 1) (τ : ℝ) :
    LipschitzOnWith 3 (deviationRhs ε τ) (Icc 0 (ε / 8)) := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  have hf : deviationRhs ε τ y - deviationRhs ε τ z =
      -(s ε τ * (2 + y + z) * (y - z)) := by
    unfold deviationRhs
    ring
  rw [Real.dist_eq, Real.dist_eq, hf, abs_neg, abs_mul,
    abs_of_nonneg (mul_nonneg (s_pos ε τ).le (by linarith [hy.1, hz.1]))]
  change s ε τ * (2 + y + z) * |y - z| ≤ 3 * |y - z|
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    _ ≤ 1 * (2 + y + z) := mul_le_mul_of_nonneg_right (s_le_one ε τ) (by linarith [hy.1, hz.1])
    _ ≤ 3 := by linarith [hy.2, hz.2]

/-- The transformed solution exists on the whole nonnegative time axis in its invariant strip. -/
theorem deviation_exists_Ici {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ e : ℝ → ℝ, e 0 = 0 ∧
      (∀ τ ∈ Ici 0, HasDerivWithinAt e (deviationRhs ε τ (e τ)) (Ici 0) τ) ∧
      MapsTo e (Ici 0) (Icc 0 (ε / 8)) := by
  apply scalarODE_exists_Ici (f := deviationRhs ε)
    (⟨le_rfl, by positivity⟩ : (0 : ℝ) ∈ Icc 0 (ε / 8))
    (continuous_uncurry_deviationRhs ε)
    (fun _ _ => ⟨3, fun τ _ => deviationRhs_lipschitzOnWith hε₁ τ⟩)
  · intro τ _
    have hf := (forcing_bounds hε.le τ).1
    unfold deviationRhs
    apply mul_nonneg (s_pos ε τ).le
    linarith
  · intro τ _
    have hf := (forcing_bounds hε.le τ).2
    unfold deviationRhs
    apply mul_nonpos_of_nonneg_of_nonpos (s_pos ε τ).le
    nlinarith [sq_nonneg (ε / 8)]

/-- The Riccati solution of (2.7) exists globally and has the stated decomposition. -/
theorem riccati_exists_Ici {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ (Y e : ℝ → ℝ), Y = referenceY ε e ∧ Y 0 = 1 ∧
      (∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) ∧
      MapsTo e (Ici 0) (Icc 0 (ε / 8)) := by
  obtain ⟨e, he₀, he, hstrip⟩ := deviation_exists_Ici hε hε₁
  exact ⟨referenceY ε e, e, rfl, referenceY_zero he₀,
    fun τ hτ => hasDerivWithinAt_referenceY (he τ hτ), hstrip⟩

/-- The initial value problem (2.7) has at most one solution on the forward ray. -/
theorem riccati_unique_Ici {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    {Y Z : ℝ → ℝ} (hY₀ : Y 0 = 1) (hZ₀ : Z 0 = 1)
    (hY : ∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ)
    (hZ : ∀ τ ∈ Ici 0, HasDerivWithinAt Z (rhs ε τ (Z τ)) (Ici 0) τ) :
    EqOn Y Z (Ici 0) := by
  intro τ hτ
  have hy (t : ℝ) (ht : t ∈ Ici 0) := hasDerivWithinAt_deviation (hY t ht)
  have hz (t : ℝ) (ht : t ∈ Ici 0) := hasDerivWithinAt_deviation (hZ t ht)
  have hloc : EqOn (deviation ε Y) (deviation ε Z) (Icc 0 τ) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := deviationRhs ε) (s := fun _ => Icc 0 (ε / 8))
      (fun t _ => deviationRhs_lipschitzOnWith hε₁ t)
      (fun t ht => ((hy t ht.1).mono Icc_subset_Ici_self).continuousWithinAt)
      (fun t ht => (hy t ht.1).mono (Ici_subset_Ici.mpr ht.1))
      (fun t ht => riccati_deviation_bounds_Ici hε hY₀ hY ht.1)
      (fun t ht => ((hz t ht.1).mono Icc_subset_Ici_self).continuousWithinAt)
      (fun t ht => (hz t ht.1).mono (Ici_subset_Ici.mpr ht.1))
      (fun t ht => riccati_deviation_bounds_Ici hε hZ₀ hZ ht.1)
    rw [deviation_zero hY₀, deviation_zero hZ₀]
  have hdev := hloc ⟨hτ, le_rfl⟩
  rw [← congrFun (referenceY_deviation ε Y) τ, ← congrFun (referenceY_deviation ε Z) τ]
  unfold referenceY
  rw [hdev]

theorem damping_nonneg {ε τ : ℝ} (hε : 0 ≤ ε) (hτ : 0 ≤ τ) :
    0 ≤ damping ε τ := by
  have hx := x_nonneg hε τ
  unfold damping
  positivity

theorem damping_le_two {ε τ : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hτ : 0 ≤ τ) :
    damping ε τ ≤ 2 := by
  rcases le_or_gt τ 2 with ht | ht
  · have hετ : ε * τ ≤ 2 := (mul_le_of_le_one_left hτ hε₁).trans ht
    calc
      damping ε τ = (2 * ε * τ) * (x ε τ * s ε τ ^ 2) := by unfold damping; ring
      _ ≤ (2 * ε * τ) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (x_mul_s_sq_le_half ε τ) (by positivity)
      _ ≤ 2 := by linarith
  · have ht₀ : 0 < τ := by linarith
    have hετ : ε * τ = 2 * x ε τ / τ := by
      unfold x
      field_simp
    have hsq : x ε τ ^ 2 * s ε τ ^ 2 ≤ 1 := by
      nlinarith [s_sq_mul ε τ, sq_nonneg (s ε τ)]
    calc
      damping ε τ = 2 * (ε * τ) * x ε τ * s ε τ ^ 2 := by unfold damping; ring
      _ = (4 / τ) * (x ε τ ^ 2 * s ε τ ^ 2) := by rw [hετ]; ring
      _ ≤ (4 / τ) * 1 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 2 := by rw [mul_one, div_le_iff₀ ht₀]; linarith

private theorem driving_le_one {ε : ℝ} (hε : 0 ≤ ε) (τ : ℝ) : driving ε τ ≤ 1 := by
  have hx := x_nonneg hε τ
  have hs := s_pos ε τ
  unfold driving
  calc
    _ ≤ s ε τ ^ 2 * 1 := by
      exact mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hε hx]) (sq_nonneg _)
    _ ≤ 1 := by rw [mul_one]; nlinarith [s_le_one ε τ]

theorem riccati_abs_le_one {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    {Y : ℝ → ℝ} (h₀ : Y 0 = 1)
    (hY : ∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) :
    ∀ τ ∈ Ici 0, |Y τ| ≤ 1 := by
  intro τ hτ
  have hdev := (riccati_deviation_bounds_Ici hε h₀ hY hτ).1
  have hlow : -1 ≤ Y τ := by
    rw [← congrFun (referenceY_deviation ε Y) τ, referenceY]
    have hbase : 0 ≤ s ε τ * (1 + deviation ε Y τ) :=
      mul_nonneg (s_pos ε τ).le (by linarith)
    linarith [damping_le_two hε.le hε₁ hτ]
  have hhigh : Y τ ≤ 1 := by
    apply scalar_le_of_derivWithinAt_nonpos_Ici hY h₀.le _ τ hτ
    intro t ht hYt
    have hdamp := mul_nonneg (damping_nonneg hε.le ht) (show 0 ≤ Y t by linarith)
    unfold rhs
    nlinarith [driving_le_one hε.le t, sq_nonneg (Y t - 1)]
  exact abs_le.mpr ⟨hlow, hhigh⟩

private theorem rhs_zero_neg {ε τ : ℝ} (h₂ : 2 ≤ ε * τ) : rhs ε τ 0 < 0 := by
  have hx : ε * x ε τ = (ε * τ) ^ 2 / 2 := by unfold x; ring
  have hval : 1 - ε * x ε τ < 0 := by rw [hx]; nlinarith [sq_nonneg (ε * τ - 2)]
  simpa [rhs, driving] using mul_neg_of_pos_of_neg (pow_pos (s_pos ε τ) 2) hval

/-- The global Riccati solution has one zero and satisfies the two strict sign conditions. -/
theorem riccati_turning_time {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    {Y e : ℝ → ℝ} (hY : ∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ)
    (hform : Y = referenceY ε e) (he : MapsTo e (Ici 0) (Icc 0 (ε / 8))) :
    ∃ τm ∈ Icc (2 / ε) (3 / ε), Y τm = 0 ∧
      (∀ τ ∈ Ico 0 τm, 0 < Y τ) ∧ (∀ τ ∈ Ioi τm, Y τ < 0) := by
  let a : ℝ := 2 / ε
  let b : ℝ := 3 / ε
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hab : a ≤ b := div_le_div_of_nonneg_right (by norm_num) hε.le
  have hapos : 0 < Y a := by
    rw [hform]
    have h : ε * a = 2 := by dsimp [a]; field_simp
    exact referenceY_pos hε.le h.le (he ha).1
  have hbneg : Y b < 0 := by
    rw [hform]
    have h : ε * b = 3 := by dsimp [b]; field_simp
    exact referenceY_neg_at_three hε hε₁ h (he (ha.trans hab)).2
  have hc : ContinuousOn Y (Ici 0) := fun t ht => (hY t ht).continuousWithinAt
  have habsub : Icc a b ⊆ Ici (0 : ℝ) := fun _ ht => ha.trans ht.1
  obtain ⟨τm, hm, hz⟩ := intermediate_value_Icc' hab (hc.mono habsub)
    (show (0 : ℝ) ∈ Icc (Y b) (Y a) from ⟨hbneg.le, hapos.le⟩)
  have hsign : ∀ t ∈ Ici a, Y t = 0 → rhs ε t (Y t) < 0 := by
    intro t ht ht₀
    rw [ht₀]
    apply rhs_zero_neg
    exact (div_le_iff₀ hε).mp ht |>.trans_eq (mul_comm t ε)
  refine ⟨τm, hm, hz, ?_, ?_⟩
  · intro t ht
    rcases le_or_gt a t with hle | hlt
    · by_contra! hnonpos
      have hn := scalar_lt_of_derivWithinAt_neg_at_boundary_Ici hY (ha.trans hle)
        hnonpos (fun u hu => hsign u (hle.trans hu)) τm ht.2
      exact (ne_of_lt hn) hz
    · rw [hform]
      have h : ε * t ≤ 2 := by
        rw [mul_comm, ← le_div_iff₀ hε]
        exact hlt.le
      exact referenceY_pos hε.le h (he ht.1).1
  · exact scalar_lt_of_derivWithinAt_neg_at_boundary_Ici hY (ha.trans hm.1) hz.le
      (fun t ht => hsign t (hm.1.trans ht))

private theorem referenceY_lower_on_initial_window {ε τ : ℝ} (hε : 0 < ε)
    (hτ : τ ∈ Icc 0 (Real.sqrt (2 / ε))) {e : ℝ → ℝ} (he : 0 ≤ e τ) :
    (Real.sqrt 2)⁻¹ - ε * τ / 4 ≤ referenceY ε e τ := by
  have hx₀ := x_nonneg hε.le τ
  have hx : x ε τ ≤ 1 := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1 hτ.2 2) hε.le
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 / ε),
      mul_div_cancel₀ _ hε.ne'] at hp
    unfold x
    linarith
  have hs : (Real.sqrt 2)⁻¹ ≤ s ε τ := by
    unfold s
    apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg hx₀ (sub_nonneg.mpr hx)]
  have hdamp : damping ε τ / 4 ≤ ε * τ / 4 := by
    have h := mul_le_mul_of_nonneg_left (x_mul_s_sq_le_half ε τ)
      (mul_nonneg hε.le hτ.1)
    unfold damping
    linarith
  unfold referenceY
  nlinarith [mul_nonneg (s_pos ε τ).le he]

/-- The logarithmic gain in Lemma 2.4 follows by integrating the lower envelope
on the initial window through the time at which the clock is one. -/
theorem riccati_gain_bound {ε τm : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hm : 2 / ε ≤ τm) {Y e : ℝ → ℝ} (hform : Y = referenceY ε e)
    (he : MapsTo e (Ici 0) (Icc 0 (ε / 8))) (hYc : ContinuousOn Y (Ici 0))
    (hnonneg : ∀ τ ∈ Icc 0 τm, 0 ≤ Y τ) :
    (Real.sqrt ε)⁻¹ - 1 ≤ ∫ τ in 0..τm, Y τ := by
  let T := Real.sqrt (2 / ε)
  have hT₀ : 0 ≤ T := Real.sqrt_nonneg _
  have hT : T ≤ τm := by
    apply le_trans _ hm
    apply (Real.sqrt_le_left (by positivity)).mpr
    have h : 1 ≤ (2 : ℝ) / ε := (le_div_iff₀ hε).mpr (by linarith)
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) / ε by positivity) (sub_nonneg.mpr h)]
  have hYint {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable Y MeasureTheory.volume a b :=
    (hYc.mono (fun _ ht => ha.trans ((uIcc_of_le hab).subset ht).1)).intervalIntegrable
  let g (τ : ℝ) := (Real.sqrt 2)⁻¹ - ε * τ / 4
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hgI : IntervalIntegrable g MeasureTheory.volume 0 T := hgc.intervalIntegrable _ _
  have hlower := intervalIntegral.integral_mono_on hT₀ hgI (hYint le_rfl hT₀) (f := g) (g := Y)
      (fun τ hτ => hform ▸ referenceY_lower_on_initial_window hε hτ (he hτ.1).1)
  let G (τ : ℝ) := (Real.sqrt 2)⁻¹ * τ - ε * τ ^ 2 / 8
  have hG (τ : ℝ) : HasDerivAt G (g τ) τ := by
    have h := ((hasDerivAt_id τ).const_mul (Real.sqrt 2)⁻¹).sub
      (((hasDerivAt_pow (𝕜 := ℝ) 2 τ).const_mul ε).div_const 8)
    apply h.congr_deriv
    simp only [g, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hg : (∫ τ in 0..T, g τ) = G T - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hG τ) hgI
  have hmain : G T - G 0 = (Real.sqrt ε)⁻¹ - 1 / 4 := by
    have hmul : (Real.sqrt 2)⁻¹ * T = (Real.sqrt ε)⁻¹ := by
      dsimp [T]
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hε)]
    have hsq : ε * T ^ 2 / 8 = 1 / 4 := by
      dsimp [T]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 / ε),
        mul_div_cancel₀ _ hε.ne']
      norm_num
    simp [G, hmul, hsq]
  have htail : 0 ≤ ∫ τ in T..τm, Y τ :=
    intervalIntegral.integral_nonneg hT fun τ hτ => hnonneg τ ⟨hT₀.trans hτ.1, hτ.2⟩
  rw [hg, hmain] at hlower
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hYint le_rfl hT₀) (hYint hT₀ hT)
  linarith

/-- The global existence, two-sided bound, turning time, and gain of Lemma 2.4. -/
theorem riccati_reference_solution {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ (Y e : ℝ → ℝ) (τm : ℝ), Y = referenceY ε e ∧ Y 0 = 1 ∧
      (∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) ∧
      MapsTo e (Ici 0) (Icc 0 (ε / 8)) ∧
      (∀ τ ∈ Ici 0, |Y τ| ≤ 1) ∧
      τm ∈ Icc (2 / ε) (3 / ε) ∧ Y τm = 0 ∧
      (∀ τ ∈ Ico 0 τm, 0 < Y τ) ∧ (∀ τ ∈ Ioi τm, Y τ < 0) ∧
      (Real.sqrt ε)⁻¹ - 1 ≤ ∫ τ in 0..τm, Y τ := by
  obtain ⟨Y, e, hform, h₀, hY, he⟩ := riccati_exists_Ici hε hε₁
  obtain ⟨τm, hm, hz, hpos, hneg⟩ := riccati_turning_time hε hε₁ hY hform he
  refine ⟨Y, e, τm, hform, h₀, hY, he, riccati_abs_le_one hε hε₁ h₀ hY,
    hm, hz, hpos, hneg, riccati_gain_bound hε hε₁ hm.1 hform he
      (fun τ hτ => (hY τ hτ).continuousWithinAt) ?_⟩
  intro τ hτ
  rcases hτ.2.lt_or_eq with hlt | rfl
  · exact (hpos τ ⟨hτ.1, hlt⟩).le
  · exact hz.ge

/-- The positive reference amplitude in the second coordinate. -/
def referenceV (Y : ℝ → ℝ) (τ : ℝ) : ℝ :=
  Real.exp (∫ t in 0..τ, Y t)

/-- The first coordinate of the growing reference path. -/
def referenceU (Y : ℝ → ℝ) (τ : ℝ) : ℝ :=
  Y τ * referenceV Y τ

theorem referenceV_pos (Y : ℝ → ℝ) (τ : ℝ) : 0 < referenceV Y τ :=
  Real.exp_pos _

@[simp] theorem referenceV_zero (Y : ℝ → ℝ) : referenceV Y 0 = 1 :=
  by simp [referenceV]

theorem referenceU_zero {Y : ℝ → ℝ} (h₀ : Y 0 = 1) : referenceU Y 0 = 1 :=
  by simp [referenceU, h₀]

theorem hasDerivWithinAt_referenceV {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0))
    {τ : ℝ} (hτ : τ ∈ Ici 0) :
    HasDerivWithinAt (referenceV Y) (referenceU Y τ) (Ici 0) τ := by
  let extended (t : ℝ) := Y (max 0 t)
  have hc : Continuous extended :=
    hYc.comp_continuous (continuous_const.max continuous_id) (fun t => mem_Ici.mpr (le_max_left (0 : ℝ) t))
  have hprim : HasDerivWithinAt (fun u => ∫ t in 0..u, Y t) (Y τ) (Ici 0) τ := by
    have hd := (hc.integral_hasStrictDerivAt 0 τ).hasDerivAt.hasDerivWithinAt (s := Ici 0)
    have heq : extended τ = Y τ := by dsimp [extended]; rw [max_eq_right hτ]
    rw [heq] at hd
    apply hd.congr_of_mem _ hτ
    intro t ht
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht]
    intro u hu
    dsimp [extended]
    rw [max_eq_right hu.1]
  exact hprim.exp.congr_deriv (by unfold referenceU referenceV; ring)

/-- The reference amplitudes satisfy the two equations of (2.6). -/
theorem reference_amplitudes_solve {ε : ℝ} {Y : ℝ → ℝ}
    (hY : ∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) :
    ∀ τ ∈ Ici 0,
      HasDerivWithinAt (referenceU Y)
        (driving ε τ * referenceV Y τ - damping ε τ * referenceU Y τ) (Ici 0) τ ∧
      HasDerivWithinAt (referenceV Y) (referenceU Y τ) (Ici 0) τ := by
  intro τ hτ
  have hV := hasDerivWithinAt_referenceV (fun t ht => (hY t ht).continuousWithinAt) hτ
  refine ⟨((hY τ hτ).mul hV).congr_deriv ?_, hV⟩
  unfold referenceU rhs
  ring

end

end TorusEuler.ReferenceRiccati
