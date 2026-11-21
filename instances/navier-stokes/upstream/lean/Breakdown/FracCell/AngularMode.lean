import Breakdown.FracCell.StAngularMode
import Breakdown.FracCell.StCircleWeak

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis CellEnergy

namespace Internal.AngularMode

def turnUnit (θ : ℝ) : Fin 3 → Space := ![angularUnit θ, -radialUnit θ, 0]

def fc (v : Space → Space) (l : Fin 3) (y : Space) : ℝ := inner ℝ (v y) (unitVector l)

def gc (G : Space → (Space →L[ℝ] Space)) (l : Fin 3) (y : Space) : Space :=
  ∑ i : Fin 3, inner ℝ (G y (unitVector i)) (unitVector l) • unitVector i

def wt (k : ℝ) (a l : Fin 3) (θ : ℝ) : ℂ :=
  Complex.exp (-(k * θ : ℝ) * Complex.I) * ((frameUnit θ a l : ℝ) : ℂ)

theorem vec_expand (u : Space) : u = ∑ i : Fin 3, u i • unitVector i := by
  ext j
  fin_cases j <;> simp [unitVector, Fin.sum_univ_three]

theorem unit_inner (i : Fin 3) (u : Space) : inner ℝ (unitVector i) u = u i := by
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem inner_comp (u w : Space) : inner ℝ u w = ∑ l : Fin 3, w l * inner ℝ u (unitVector l) := by
  conv_lhs => rw [vec_expand w]
  simp only [inner_sum, real_inner_smul_right]

theorem gc_inner (G : Space → (Space →L[ℝ] Space)) (l : Fin 3) (y w : Space) :
    inner ℝ (gc G l y) w = ∑ i : Fin 3, inner ℝ (G y (unitVector i)) (unitVector l) * w i := by
  simp only [gc, sum_inner, real_inner_smul_left, unit_inner]

theorem mat_inner (M : Space →L[ℝ] Space) (u w : Space) :
    inner ℝ (M u) w = ∑ l : Fin 3, w l * inner ℝ (∑ i : Fin 3, inner ℝ (M (unitVector i)) (unitVector l) • unitVector i) u := by
  rw [inner_comp (M u) w]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  conv_lhs => rw [vec_expand u]
  simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, unit_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem unit_hasDeriv (a l : Fin 3) (θ : ℝ) :
    HasDerivAt (fun t => frameUnit t a l) (turnUnit θ a l) θ := by
  fin_cases a <;> fin_cases l <;>
    simp [frameUnit, turnUnit, radialUnit, angularUnit, axialUnit]
  all_goals first
    | exact Real.hasDerivAt_cos θ
    | exact Real.hasDerivAt_sin θ
    | exact (Real.hasDerivAt_sin θ).neg
    | exact (Real.hasDerivAt_cos θ).neg
    | exact hasDerivAt_const θ _

theorem unit_smooth (a l : Fin 3) : ContDiff ℝ ∞ (fun t => frameUnit t a l) := by
  fin_cases a <;> fin_cases l <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit]
  all_goals first
    | exact Real.contDiff_cos
    | exact Real.contDiff_sin
    | exact Real.contDiff_sin.neg
    | exact contDiff_const

theorem unit_periodic (a l : Fin 3) : Function.Periodic (fun t => frameUnit t a l) (2 * Real.pi) := by
  intro t
  fin_cases a <;> fin_cases l <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem exp_hasDeriv (k θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(k * t : ℝ) * Complex.I))
      (Complex.exp (-(k * θ : ℝ) * Complex.I) * (-(k : ℂ) * Complex.I)) θ := by
  have hlin : HasDerivAt (fun t : ℝ => (-(k * t : ℝ) * Complex.I : ℂ)) (-(k : ℂ) * Complex.I) θ := by
    have h1 := ((hasDerivAt_id θ).const_mul k).ofReal_comp.neg.mul_const Complex.I
    exact (h1 : HasDerivAt (fun t : ℝ => (-(k * t : ℝ) * Complex.I : ℂ)) _ θ).congr_deriv (by simp)
  exact hlin.cexp

theorem wt_hasDeriv (k : ℝ) (a l : Fin 3) (θ : ℝ) :
    HasDerivAt (wt k a l) (Complex.exp (-(k * θ : ℝ) * Complex.I) *
      (-(k : ℂ) * Complex.I * ((frameUnit θ a l : ℝ) : ℂ) + ((turnUnit θ a l : ℝ) : ℂ))) θ := by
  have h := (exp_hasDeriv k θ).mul (unit_hasDeriv a l θ).ofReal_comp
  refine (h : HasDerivAt (wt k a l) _ θ).congr_deriv ?_
  ring

theorem wt_deriv (k : ℝ) (a l : Fin 3) (θ : ℝ) :
    deriv (wt k a l) θ = Complex.exp (-(k * θ : ℝ) * Complex.I) *
      (-(k : ℂ) * Complex.I * ((frameUnit θ a l : ℝ) : ℂ) + ((turnUnit θ a l : ℝ) : ℂ)) :=
  (wt_hasDeriv k a l θ).deriv

theorem wt_smooth (k : ℝ) (a l : Fin 3) : ContDiff ℝ ∞ (wt k a l) := by
  have hE : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (-(k * t : ℝ) * Complex.I)) := by
    have hlin : ContDiff ℝ ∞ (fun t : ℝ => (-(k * t : ℝ) * Complex.I : ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).neg.mul contDiff_const
    exact Complex.contDiff_exp.comp hlin
  exact hE.mul (Complex.ofRealCLM.contDiff.comp (unit_smooth a l))

theorem wt_periodic (j : ℤ) (a l : Fin 3) : Function.Periodic (wt (j : ℝ) a l) (2 * Real.pi) := by
  intro θ
  simp only [wt]
  have e := unit_periodic a l θ
  simp only at e
  rw [e]
  congr 1
  have : (-(((j : ℝ) * (θ + 2 * Real.pi) : ℝ) : ℂ)) * Complex.I =
      -(((j : ℝ) * θ : ℝ) : ℂ) * Complex.I + ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem ii_cmul {f : ℝ → ℝ} {g : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (hg : Continuous g) :
    IntervalIntegrable (fun θ => g θ * (f θ : ℂ)) volume 0 (2 * Real.pi) := by
  have h : IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 (2 * Real.pi) := ⟨hf.1.ofReal, hf.2.ofReal⟩
  exact h.continuousOn_mul hg.continuousOn

theorem ii_sum {F : Fin 3 → ℝ → ℂ} (h : ∀ l, IntervalIntegrable (F l) volume 0 (2 * Real.pi)) :
    IntervalIntegrable (fun θ => ∑ l : Fin 3, F l θ) volume 0 (2 * Real.pi) := by
  simp only [Fin.sum_univ_three]
  exact ((h 0).add (h 1)).add (h 2)

theorem int_sum {F : Fin 3 → ℝ → ℂ} (h : ∀ l, IntervalIntegrable (F l) volume 0 (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ l : Fin 3, F l θ =
      ∑ l : Fin 3, ∫ θ in (0 : ℝ)..(2 * Real.pi), F l θ :=
  intervalIntegral.integral_finsetSum fun l _ => h l

theorem frameVec_eq (θ : ℝ) (u : Space) (b : Fin 3) :
    frameVec θ u b = ∑ l : Fin 3, frameUnit θ b l * inner ℝ u (unitVector l) := by
  rw [← inner_comp]
  fin_cases b <;> rfl

theorem frameMat_eq (θ : ℝ) (r : ℝ) (G : Space → (Space →L[ℝ] Space)) (y : Space) (a : Fin 3) :
    r * frameMat θ (G y) a 1 = ∑ l : Fin 3, frameUnit θ a l * (r * inner ℝ (gc G l y) (angularUnit θ)) := by
  have e : frameMat θ (G y) a 1 = inner ℝ (G y (angularUnit θ)) (frameUnit θ a) := rfl
  rw [e, mat_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [gc]
  ring

theorem mode_eq (m : ℕ) (n : ℤ) (v : Space → Space) (r z : ℝ) (b : Fin 3) :
    modeVec m n v r z b = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      ∑ l : Fin 3, wt (azimuth m n) b l θ * ((fc v l (cylPoint r θ z) : ℝ) : ℂ) := by
  simp only [modeVec]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [frameVec_eq, wt, fc, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem grad_eq (m : ℕ) (n : ℤ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (a : Fin 3) (r z : ℝ)
    (hf : ∀ l, IntervalIntegrable (fun θ => fc v l (cylPoint r θ z)) volume 0 (2 * Real.pi))
    (hg : ∀ l, IntervalIntegrable (fun θ => inner ℝ (gc G l (cylPoint r θ z)) (angularUnit θ))
      volume 0 (2 * Real.pi))
    (hid : ∀ l, ∫ θ in (0 : ℝ)..(2 * Real.pi), wt (azimuth m n) a l θ *
        ((r * inner ℝ (gc G l (cylPoint r θ z)) (angularUnit θ) : ℝ) : ℂ) =
      -∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (wt (azimuth m n) a l) θ * ((fc v l (cylPoint r θ z) : ℝ) : ℂ)) :
    (r : ℂ) * gradMode m n G a 1 (r, z) = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      ∑ l : Fin 3, -deriv (wt (azimuth m n) a l) θ * ((fc v l (cylPoint r θ z) : ℝ) : ℂ) := by
  have hI : ∀ l, IntervalIntegrable (fun θ => wt (azimuth m n) a l θ *
      ((r * inner ℝ (gc G l (cylPoint r θ z)) (angularUnit θ) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    fun l => ii_cmul ((hg l).const_mul r) (wt_smooth _ a l).continuous
  have hJ : ∀ l, IntervalIntegrable (fun θ => -deriv (wt (azimuth m n) a l) θ *
      ((fc v l (cylPoint r θ z) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    fun l => ii_cmul (hf l) ((wt_smooth _ a l).continuous_deriv (by simp)).neg
  rw [int_sum hJ]
  have step : ∀ l, ∫ θ in (0 : ℝ)..(2 * Real.pi), -deriv (wt (azimuth m n) a l) θ *
      ((fc v l (cylPoint r θ z) : ℝ) : ℂ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), wt (azimuth m n) a l θ *
        ((r * inner ℝ (gc G l (cylPoint r θ z)) (angularUnit θ) : ℝ) : ℂ) := by
    intro l
    simp only [neg_mul, intervalIntegral.integral_neg]
    rw [hid l]
  simp only [step]
  rw [← int_sum hI]
  simp only [gradMode, modeMat]
  rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have h := congrArg (fun x : ℝ => (x : ℂ)) (frameMat_eq θ r G (cylPoint r θ z) a)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h
  simp only [wt]
  calc (r : ℂ) * (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          ((frameMat θ (G (cylPoint r θ z)) a 1 : ℝ) : ℂ))
      = Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          ((r : ℂ) * ((frameMat θ (G (cylPoint r θ z)) a 1 : ℝ) : ℂ)) := by ring
    _ = _ := by
      rw [h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      push_cast
      ring

theorem comb {X Y Z : ℝ → ℂ} (hY : IntervalIntegrable Y volume 0 (2 * Real.pi))
    (hZ : IntervalIntegrable Z volume 0 (2 * Real.pi)) (c d : ℂ) (h : ∀ θ, X θ = c * Y θ + d * Z θ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), X θ =
      c * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Y θ) +
        d * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Z θ) := by
  rw [intervalIntegral.integral_congr (fun θ _ => h θ),
    intervalIntegral.integral_add (hY.const_mul c) (hZ.const_mul d),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem point (m : ℕ) (n : ℤ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ)
    (hf : ∀ l, IntervalIntegrable (fun θ => fc v l (cylPoint r θ z)) volume 0 (2 * Real.pi))
    (hg : ∀ l, IntervalIntegrable (fun θ => inner ℝ (gc G l (cylPoint r θ z)) (angularUnit θ))
      volume 0 (2 * Real.pi))
    (hid : ∀ a l, ∫ θ in (0 : ℝ)..(2 * Real.pi), wt (azimuth m n) a l θ *
        ((r * inner ℝ (gc G l (cylPoint r θ z)) (angularUnit θ) : ℝ) : ℂ) =
      -∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (wt (azimuth m n) a l) θ * ((fc v l (cylPoint r θ z) : ℝ) : ℂ)) :
    (r : ℂ) * gradMode m n G 0 1 (r, z) =
          ((azimuth m n : ℂ) * Complex.I) * modeVec m n v r z 0 - modeVec m n v r z 1 ∧
      (r : ℂ) * gradMode m n G 1 1 (r, z) =
          ((azimuth m n : ℂ) * Complex.I) * modeVec m n v r z 1 + modeVec m n v r z 0 ∧
      (r : ℂ) * gradMode m n G 2 1 (r, z) = ((azimuth m n : ℂ) * Complex.I) * modeVec m n v r z 2 := by
  have hT : ∀ b, IntervalIntegrable (fun θ => ∑ l : Fin 3, wt (azimuth m n) b l θ *
      ((fc v l (cylPoint r θ z) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    fun b => ii_sum fun l => ii_cmul (hf l) (wt_smooth _ b l).continuous
  simp only [mode_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [grad_eq m n v G 0 r z hf hg (hid 0), comb (hT 0) (hT 1) ((azimuth m n : ℂ) * Complex.I) (-1)]
    · ring
    · intro θ
      simp only [wt_deriv, wt, turnUnit, frameUnit, Fin.sum_univ_three]
      simp
      ring
  · rw [grad_eq m n v G 1 r z hf hg (hid 1), comb (hT 1) (hT 0) ((azimuth m n : ℂ) * Complex.I) 1]
    · ring
    · intro θ
      simp only [wt_deriv, wt, turnUnit, frameUnit, Fin.sum_univ_three]
      simp
      ring
  · rw [grad_eq m n v G 2 r z hf hg (hid 2), comb (hT 2) (hT 2) ((azimuth m n : ℂ) * Complex.I) 0]
    · ring
    · intro θ
      simp only [wt_deriv, wt, turnUnit, frameUnit, Fin.sum_univ_three]
      simp
      ring

theorem loc_col {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (h2 : Integrable (fun y => entrySq (G y))) (i : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector i)) volume := by
  have hs : AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hG
  have hsq : Integrable (fun y => ‖G y (unitVector i)‖ ^ 2) volume :=
    h2.mono' (hs.norm.pow 2) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i))
  exact ((memLp_two_iff_integrable_sq_norm hs).2 hsq).locallyIntegrable (by norm_num)

theorem loc_inner {X : Space → Space} (hX : LocallyIntegrable X volume) (w : Space) :
    LocallyIntegrable (fun y => inner ℝ (X y) w) volume :=
  locallyIntegrable_iff.2 fun _ hK => (hX.integrableOn_isCompact hK).inner_const w

end Internal.AngularMode

open Internal.AngularMode in
theorem angularMode (hC : CircleWeakStatement) : AngularModeStatement := by
  intro m v G _ hs n
  have locv : LocallyIntegrable v volume := hs.velocity_six.locallyIntegrable (by norm_num)
  have locG := loc_col hs.measurable_gradient hs.gradient_two
  have locf : ∀ l, LocallyIntegrable (fc v l) volume := fun l => loc_inner locv (unitVector l)
  have locg : ∀ l, LocallyIntegrable (gc G l) volume := by
    intro l
    unfold gc
    refine locallyIntegrable_finsetSum Finset.univ fun i _ => ?_
    exact locallyIntegrable_iff.2 fun K hK =>
      ((loc_inner (locG i) (unitVector l)).integrableOn_isCompact hK).smul_const _
  have hweak : ∀ l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * fc v l y = -∫ y, φ y * inner ℝ (gc G l y) (unitVector j) := by
    intro l φ hφ j
    have hw := hs.weak_gradient φ hφ j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := locv.integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locG j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * fc v l y
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • v y) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, fc, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • v y) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • G y (unitVector j)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • G y (unitVector j)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gc G l y) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gc_inner]
          simp [L, innerSL_apply_apply, real_inner_comm, unitVector]
  have hK := fun l => hC (fc v l) (gc G l) (locf l) (locg l) (hweak l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun l => (hK l).1
  have hid := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun l =>
    (hK l).2 (wt (azimuth m n) a l) (wt_smooth _ a l) (hk ▸ wt_periodic _ a l)
  filter_upwards [hint, hid] with p h1 h2 hr
  obtain ⟨r, z⟩ := p
  exact point m n v G r z (fun l => (h1 l hr).1) (fun l => (h1 l hr).2) (fun a l => h2 a l hr)

end Breakdown.CellCert.CellFormula
