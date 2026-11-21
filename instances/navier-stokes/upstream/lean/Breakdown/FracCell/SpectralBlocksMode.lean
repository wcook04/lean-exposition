import Breakdown.FracCell.SpectralBlocksSplit

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def cylPoint (r θ z : ℝ) : Space :=
  EuclideanSpace.single 0 (r * Real.cos θ) + EuclideanSpace.single 1 (r * Real.sin θ) + EuclideanSpace.single 2 z

def CylStatement : Prop :=
  ∀ f : Space → ℝ, Integrable f →
    ∫ y, f y = ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
      q.1 * ∫ θ in (-Real.pi)..Real.pi, f (cylPoint q.1 θ q.2)

namespace Internal.SpectralBlocksMode

def frameAt (c : Fin 3) (θ : ℝ) : Space :=
  match c with
  | 0 => EuclideanSpace.single 0 (Real.cos θ) + EuclideanSpace.single 1 (Real.sin θ)
  | 1 => EuclideanSpace.single 0 (-Real.sin θ) + EuclideanSpace.single 1 (Real.cos θ)
  | 2 => unitVector 2

theorem frame_eq (c : Fin 3) (y : Space) : frameVector c y = frameAt c (angleCoord y) := by
  fin_cases c <;> rfl

theorem frame_inner (c c' : Fin 3) (θ : ℝ) :
    inner ℝ (frameAt c θ) (frameAt c' θ) = if c = c' then 1 else 0 := by
  fin_cases c <;> fin_cases c' <;>
    simp only [frameAt, unitVector, inner_add_left, inner_add_right, EuclideanSpace.inner_single_left] <;>
    simp <;>
    first | ring1 | linear_combination Real.cos_sq_add_sin_sq θ

theorem inner_frame_sum (A B : Fin 3 → ℝ) (θ : ℝ) :
    inner ℝ (∑ c : Fin 3, A c • frameAt c θ) (∑ c : Fin 3, B c • frameAt c θ) = ∑ c : Fin 3, A c * B c := by
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, frame_inner]
  simp [Fin.sum_univ_three]
  ring

theorem cyl0 (r θ z : ℝ) : cylPoint r θ z 0 = r * Real.cos θ := by simp [cylPoint]

theorem cyl1 (r θ z : ℝ) : cylPoint r θ z 1 = r * Real.sin θ := by simp [cylPoint]

theorem cyl2 (r θ z : ℝ) : cylPoint r θ z 2 = z := by simp [cylPoint]

theorem radial_cyl {r : ℝ} (hr : 0 < r) (θ z : ℝ) : radialCoord (cylPoint r θ z) = r := by
  rw [radialCoord, cyl0, cyl1]
  have e : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ
  rw [e, Real.sqrt_sq hr.le]

theorem angle_cyl {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) (z : ℝ) :
    angleCoord (cylPoint r θ z) = θ := by
  rw [angleCoord, cyl0, cyl1]
  have e : (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) =
      (r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [e, Complex.arg_real_mul _ hr, Complex.arg_cos_add_sin_mul_I hθ]

theorem trig_int (u : Fin 2) (m : ℤ) (hm : m ≠ 0) :
    ∫ θ in (-π)..π, trigMode u ((m : ℝ) * θ) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  fin_cases u
  · simp only [trigMode, Fin.zero_eta, if_true]
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm', integral_cos]
    simp [mul_neg, Real.sin_neg, Real.sin_int_mul_pi]
  · simp only [trigMode, Fin.mk_one, one_ne_zero, if_false]
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hm', integral_sin]
    simp [mul_neg, Real.cos_neg]

theorem trig_prod (t t' : Fin 2) : ∃ (u : Fin 2) (σ₁ σ₂ : ℝ), ∀ a b : ℝ,
    trigMode t a * trigMode t' b = σ₁ * trigMode u (a - b) + σ₂ * trigMode u (a + b) := by
  fin_cases t <;> fin_cases t'
  · refine ⟨0, 1 / 2, 1 / 2, fun a b => ?_⟩
    simp only [trigMode, Fin.zero_eta, if_true, Real.cos_sub, Real.cos_add]
    ring
  · refine ⟨1, -(1 / 2), 1 / 2, fun a b => ?_⟩
    simp only [trigMode, Fin.zero_eta, Fin.mk_one, if_true, one_ne_zero, if_false, Real.sin_sub, Real.sin_add]
    ring
  · refine ⟨1, 1 / 2, 1 / 2, fun a b => ?_⟩
    simp only [trigMode, Fin.zero_eta, Fin.mk_one, if_true, one_ne_zero, if_false, Real.sin_sub, Real.sin_add]
    ring
  · refine ⟨0, 1 / 2, -(1 / 2), fun a b => ?_⟩
    simp only [trigMode, Fin.mk_one, one_ne_zero, if_false, if_true, Real.cos_sub, Real.cos_add]
    ring

theorem trig_cont (u : Fin 2) (m : ℝ) : Continuous fun θ : ℝ => trigMode u (m * θ) := by
  unfold trigMode
  split_ifs
  · fun_prop
  · fun_prop

theorem trig_orth (t t' : Fin 2) {k k' : ℕ} (h : k ≠ k') :
    ∫ θ in (-π)..π, trigMode t ((k : ℝ) * θ) * trigMode t' ((k' : ℝ) * θ) = 0 := by
  have hd : ((k : ℤ) - k' : ℤ) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  have hs : ((k : ℤ) + k' : ℤ) ≠ 0 := by
    intro h0
    have : k = 0 ∧ k' = 0 := by omega
    exact h (this.1.trans this.2.symm)
  obtain ⟨u, σ₁, σ₂, hp⟩ := trig_prod t t'
  have e : ∀ θ : ℝ, trigMode t ((k : ℝ) * θ) * trigMode t' ((k' : ℝ) * θ) =
      σ₁ * trigMode u ((((k : ℤ) - k' : ℤ) : ℝ) * θ) + σ₂ * trigMode u ((((k : ℤ) + k' : ℤ) : ℝ) * θ) := by
    intro θ
    rw [hp, show (k : ℝ) * θ - k' * θ = (((k : ℤ) - k' : ℤ) : ℝ) * θ by push_cast; ring,
      show (k : ℝ) * θ + k' * θ = (((k : ℤ) + k' : ℤ) : ℝ) * θ by push_cast; ring]
  simp only [e]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    trig_int u _ hd, trig_int u _ hs]
  · ring
  · exact (continuous_const.mul (trig_cont u _)).intervalIntegrable _ _
  · exact (continuous_const.mul (trig_cont u _)).intervalIntegrable _ _

theorem solid_iff (g : CellBlock) (s : Fin 2) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    cylPoint r θ z ∈ cellSolid g s ↔ cylPoint r 0 z ∈ cellSolid g s := by
  simp only [cellSolid, Set.mem_setOf_eq, radial_cyl hr, cyl2]

theorem ite_smul_one {P : Prop} [Decidable P] (v : Space) :
    (if P then v else 0) = (if P then (1 : ℝ) else 0) • v := by
  split_ifs <;> simp

open Classical in
theorem shape_cyl (g : CellBlock) (a : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-π) π) (z : ℝ) :
    shapeField g a (cylPoint r θ z) = ∑ s : Fin 2, (if cylPoint r 0 z ∈ cellSolid g s then (1 : ℝ) else 0) •
      ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * θ) * a s c t r z) • frameAt c θ := by
  classical
  unfold shapeField
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Set.indicator_apply]
  simp only [solid_iff g s hr θ z, frame_eq, angle_cyl hr hθ, radial_cyl hr, cyl2]
  rw [ite_smul_one]

open Classical in
def cylCoef (g g' : CellBlock) (a b : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (r z : ℝ) (t t' : Fin 2) : ℝ :=
  ∑ s : Fin 2, ∑ s' : Fin 2, (if cylPoint r 0 z ∈ cellSolid g s then (1 : ℝ) else 0) *
    (if cylPoint r 0 z ∈ cellSolid g' s' then (1 : ℝ) else 0) * ∑ c : Fin 3, a s c t r z * b s' c t' r z

theorem inner_cyl (g g' : CellBlock) (a b : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) (z : ℝ) :
    inner ℝ (shapeField g a (cylPoint r θ z)) (shapeField g' b (cylPoint r θ z)) =
      ∑ t : Fin 2, ∑ t' : Fin 2, cylCoef g g' a b r z t t' *
        (trigMode t (g.mode * θ) * trigMode t' (g'.mode * θ)) := by
  classical
  rw [shape_cyl g a hr hθ z, shape_cyl g' b hr hθ z]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, frame_inner]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [cylCoef, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

end Internal.SpectralBlocksMode

open Internal.SpectralBlocks Internal.SpectralBlocksMode

theorem sameSolidOrth_of_cyl (hC : CylStatement) : SameSolidOrthStatement := by
  intro g g' _ _ _ _ hk F G hF hG hF2 hG2
  obtain ⟨a, -, ha⟩ := hF
  obtain ⟨b, -, hb⟩ := hG
  have hI := inner_integrable hF2 hG2
  have hae : (fun y => inner ℝ (F y) (G y)) =ᵐ[volume]
      fun y => inner ℝ (shapeField g a y) (shapeField g' b y) := by
    filter_upwards [ha, hb] with y h1 h2
    rw [h1, h2]
  rw [integral_congr_ae hae, hC _ (hI.congr hae)]
  refine (setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) (g := fun _ => (0 : ℝ))
    fun q hq => ?_).trans (by simp)
  have hr : 0 < q.1 := hq.1
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  show q.1 * ∫ θ in (-π)..π, inner ℝ (shapeField g a (cylPoint q.1 θ q.2)) (shapeField g' b (cylPoint q.1 θ q.2)) = 0
  rw [intervalIntegral.integral_of_le hpi,
    setIntegral_congr_fun measurableSet_Ioc (fun θ hθ => inner_cyl g g' a b hr hθ q.2),
    ← intervalIntegral.integral_of_le hpi]
  have hz : ∀ t t' : Fin 2, ∫ θ in (-π)..π, cylCoef g g' a b q.1 q.2 t t' *
      (trigMode t (g.mode * θ) * trigMode t' (g'.mode * θ)) = 0 := by
    intro t t'
    rw [intervalIntegral.integral_const_mul, trig_orth t t' hk, mul_zero]
  have hii : ∀ t t' : Fin 2, IntervalIntegrable (fun θ => cylCoef g g' a b q.1 q.2 t t' *
      (trigMode t (g.mode * θ) * trigMode t' (g'.mode * θ))) volume (-π) π := fun t t' =>
    (continuous_const.mul ((trig_cont t _).mul (trig_cont t' _))).intervalIntegrable _ _
  have hsum : ∫ θ in (-π)..π, ∑ t : Fin 2, ∑ t' : Fin 2, cylCoef g g' a b q.1 q.2 t t' *
      (trigMode t (g.mode * θ) * trigMode t' (g'.mode * θ)) = 0 := by
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_eq_zero fun t _ => ?_
      rw [intervalIntegral.integral_finset_sum]
      · exact Finset.sum_eq_zero fun t' _ => hz t t'
      · intro t' _
        exact hii t t'
    · intro t _
      exact (continuous_finsetSum _ fun t' _ =>
        continuous_const.mul ((trig_cont t _).mul (trig_cont t' _))).intervalIntegrable _ _
  rw [hsum, mul_zero]

theorem blockBound_of_cyl (h1 : IntervalIdentityStatement) (h2 : IntervalMinimalStatement)
    (h3 : IntervalMonotoneStatement) (h4 : IntervalClosedStatement) (h5 : AxisClosedStatement)
    (hL : BlockLocalStatement) (hC : CylStatement) : BlockBoundStatement :=
  blockBound_of_local h1 h2 h3 h4 h5 hL (sameSolidOrth_of_cyl hC)

end Spectral

end CellCert

end Breakdown
