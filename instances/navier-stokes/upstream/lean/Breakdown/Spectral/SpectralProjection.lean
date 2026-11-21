import Breakdown.Spectral.Resolvent

noncomputable section

open Metric

namespace Breakdown.Spectral

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

def specProj (T : Y →L[ℂ] Y) (ρ : ℝ) : Y →L[ℂ] Y :=
  (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, ρ), resolvent T z

def backProj (T : Y →L[ℂ] Y) (ρ R : ℝ) (n : ℕ) : Y →L[ℂ] Y :=
  (2 * Real.pi * Complex.I)⁻¹ •
    ((∮ z in C(0, R), (z ^ n)⁻¹ • resolvent T z) - ∮ z in C(0, ρ), (z ^ n)⁻¹ • resolvent T z)

theorem circleIntegrable_resolvent (T : Y →L[ℂ] Y) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hA : ∀ z : ℂ, ‖z‖ = ρ → z ∈ resolventSet ℂ T) (g : ℂ → ℂ) (hg : ContinuousOn g (sphere 0 ρ)) :
    CircleIntegrable (fun z => g z • resolvent T z) 0 ρ := by
  refine ContinuousOn.circleIntegrable hρ ?_
  refine hg.smul ((continuousOn_resolvent T).mono ?_)
  intro z hz
  exact hA z (mem_sphere_zero_iff_norm.mp hz)

theorem specProj_eq_of_annulus (T : Y →L[ℂ] Y) {ρ₁ ρ₂ : ℝ} (h0 : 0 < ρ₁) (h12 : ρ₁ ≤ ρ₂)
    (hA : ∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ ρ₂ → z ∈ resolventSet ℂ T) :
    specProj T ρ₁ = specProj T ρ₂ := by
  unfold specProj
  congr 1
  symm
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable h0 h12 Set.countable_empty
    ?_ ?_
  · refine (continuousOn_resolvent T).mono ?_
    intro z hz
    rcases hz with ⟨h1, h2⟩
    rw [mem_closedBall_zero_iff] at h1
    rw [mem_ball_zero_iff, not_lt] at h2
    exact hA z h2 h1
  · intro z hz
    rcases hz with ⟨⟨h1, h2⟩, -⟩
    rw [mem_ball_zero_iff] at h1
    rw [mem_closedBall_zero_iff, not_le] at h2
    exact differentiableAt_resolvent T (hA z h2.le h1.le)

private theorem norm_specProj_sub_one_le (T : Y →L[ℂ] Y) {R : ℝ} (hR : ‖T‖ < R) :
    ‖specProj T R - 1‖ ≤ ‖T‖ / (R - ‖T‖) := by
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg T) hR
  have hmem : ∀ z : ℂ, ‖z‖ = R → z ∈ resolventSet ℂ T := fun z hz =>
    mem_resolventSet_of_norm_le_lt le_rfl (by rw [hz]; exact hR)
  have hnz : ∀ z : ℂ, z ∈ sphere (0 : ℂ) R → z ≠ 0 := by
    intro z hz h
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at hz
    linarith
  have hr : CircleIntegrable (fun z => resolvent T z) 0 R := by
    have := circleIntegrable_resolvent T hR0.le (fun z hz => hmem z hz) (fun _ => (1 : ℂ))
      continuousOn_const
    simpa using this
  have hI1 : CircleIntegrable (fun z : ℂ => z⁻¹ • (1 : Y →L[ℂ] Y)) 0 R := by
    refine ContinuousOn.circleIntegrable hR0.le ?_
    exact (continuousOn_id.inv₀ fun z hz => hnz z hz).smul continuousOn_const
  have hc : (∮ z in C(0, R), z⁻¹ • (1 : Y →L[ℂ] Y)) = (2 * Real.pi * Complex.I) • 1 := by
    have := circleIntegral_inv_pow_smul_const (1 : Y →L[ℂ] Y) hR0 0
    simpa using this
  have hne : (2 * Real.pi * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have heq : specProj T R - 1 = (2 * Real.pi * Complex.I)⁻¹ •
      ∮ z in C(0, R), (resolvent T z - z⁻¹ • (1 : Y →L[ℂ] Y)) := by
    rw [circleIntegral.integral_sub hr hI1, hc, smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rfl
  have hb : ‖∮ z in C(0, R), (resolvent T z - z⁻¹ • (1 : Y →L[ℂ] Y))‖ ≤
      2 * Real.pi * R * (R⁻¹ * (‖T‖ * (R - ‖T‖)⁻¹)) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const hR0.le ?_
    intro z hz
    have hz' : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := hnz z hz
    have hid : resolvent T z - z⁻¹ • (1 : Y →L[ℂ] Y) = z⁻¹ • (T * resolvent T z) := by
      rw [mul_resolvent T (hmem z hz'), smul_sub, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    rw [hid, norm_smul, norm_inv, hz']
    have h1 := norm_mul_le T (resolvent T z)
    have h2 := norm_resolvent_le (le_refl ‖T‖) (show ‖T‖ < ‖z‖ by rw [hz']; exact hR)
    rw [hz'] at h2
    have h3 : ‖T * resolvent T z‖ ≤ ‖T‖ * (R - ‖T‖)⁻¹ :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hR0.le)
  have hn : ‖(2 * Real.pi * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_I, mul_one, norm_mul]
    simp [abs_of_pos Real.pi_pos]
  rw [heq, norm_smul, hn]
  have hpos : 0 < R - ‖T‖ := by linarith
  calc (2 * Real.pi)⁻¹ * ‖∮ z in C(0, R), (resolvent T z - z⁻¹ • (1 : Y →L[ℂ] Y))‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * R * (R⁻¹ * (‖T‖ * (R - ‖T‖)⁻¹))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ‖T‖ / (R - ‖T‖) := by
        field_simp

theorem specProj_large (T : Y →L[ℂ] Y) {R : ℝ} (hR : ‖T‖ < R) : specProj T R = 1 := by
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg T) hR
  have key : ∀ R' : ℝ, R ≤ R' → ‖specProj T R - 1‖ ≤ ‖T‖ / (R' - ‖T‖) := by
    intro R' hR'
    rw [specProj_eq_of_annulus T hR0 hR'
      (fun z h1 _ => mem_resolventSet_of_norm_le_lt le_rfl (lt_of_lt_of_le hR h1))]
    exact norm_specProj_sub_one_le T (lt_of_lt_of_le hR hR')
  have ht : Filter.Tendsto (fun R' : ℝ => ‖T‖ / (R' - ‖T‖)) Filter.atTop (nhds 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right Filter.atTop (-‖T‖) Filter.tendsto_id
  have h0 : ‖specProj T R - 1‖ ≤ 0 :=
    ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨R, key⟩)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

theorem commute_specProj {T A : Y →L[ℂ] Y} (h : Commute A T) (ρ : ℝ) :
    Commute A (specProj T ρ) := by
  unfold specProj
  exact (commute_circleIntegral (fun z => commute_resolvent h z) 0 ρ).smul_right _

theorem commute_backProj {T A : Y →L[ℂ] Y} (h : Commute A T) (ρ R : ℝ) (n : ℕ) :
    Commute A (backProj T ρ R n) := by
  unfold backProj
  refine Commute.smul_right (Commute.sub_right ?_ ?_) _
  · exact commute_circleIntegral (fun z => (commute_resolvent h z).smul_right _) 0 R
  · exact commute_circleIntegral (fun z => (commute_resolvent h z).smul_right _) 0 ρ

end Breakdown.Spectral
