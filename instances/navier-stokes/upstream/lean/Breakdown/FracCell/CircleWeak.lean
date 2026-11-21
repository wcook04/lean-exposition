import Breakdown.FracCell.StCircleWeak
import Breakdown.FracCell.CylChange

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis SteadyCert

namespace Internal.CircleWeak

open Breakdown.CellCert.Spectral.Internal.CylIntegral

theorem coord_cd (i : Fin 3) : ContDiff ℝ ∞ (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

theorem radius_cont : Continuous cylRadius := by
  unfold cylRadius
  exact Real.continuous_sqrt.comp (((coord_cd 0).continuous.pow 2).add ((coord_cd 1).continuous.pow 2))

theorem radius_cdAt {y : Space} (hy : 0 < cylRadius y) : ContDiffAt ℝ ∞ cylRadius y := by
  have hne : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by
    unfold cylRadius at hy; exact (Real.sqrt_pos.1 hy).ne'
  exact ((((coord_cd 0).pow 2).add ((coord_cd 1).pow 2)).contDiffAt).sqrt hne

def turn (y : Space) : Space := EuclideanSpace.single 0 (-y 1) + EuclideanSpace.single 1 (y 0)

def plane (y : Space) : ℂ := (y 0 : ℂ) + (y 1 : ℂ) * Complex.I

theorem plane_cd : ContDiff ℝ ∞ plane := by
  unfold plane
  exact (Complex.ofRealCLM.contDiff.comp (coord_cd 0)).add
    ((Complex.ofRealCLM.contDiff.comp (coord_cd 1)).mul contDiff_const)

theorem single_eq (i : Fin 3) (c : ℝ) : EuclideanSpace.single i c = c • unitVector i := by
  ext j; fin_cases i <;> fin_cases j <;> simp [unitVector]

theorem turn_eq (y : Space) : turn y = (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := by
  rw [turn, single_eq, single_eq]

theorem turn_cont : Continuous turn := by
  rw [show turn = fun y => (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 from funext turn_eq]
  exact (((coord_cd 1).continuous.neg).smul continuous_const).add
    ((coord_cd 0).continuous.smul continuous_const)

theorem turn_cyl (r θ z : ℝ) : turn (cylPoint r θ z) = r • angularUnit θ := by
  ext i; fin_cases i <;> simp [turn, cylPoint, angularUnit]

theorem plane_cyl (r θ z : ℝ) :
    plane (cylPoint r θ z) = (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
  have h0 : (cylPoint r θ z) 0 = r * Real.cos θ := by simp [cylPoint]
  have h1 : (cylPoint r θ z) 1 = r * Real.sin θ := by simp [cylPoint]
  rw [plane, h0, h1]
  push_cast
  ring

theorem radius_cyl {r : ℝ} (hr : 0 < r) (θ z : ℝ) : cylRadius (cylPoint r θ z) = r := by
  have h0 : (cylPoint r θ z) 0 = r * Real.cos θ := by simp [cylPoint]
  have h1 : (cylPoint r θ z) 1 = r * Real.sin θ := by simp [cylPoint]
  unfold cylRadius
  rw [h0, h1, show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
    linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ, Real.sqrt_sq hr.le]

theorem height_cyl (r θ z : ℝ) : (cylPoint r θ z) 2 = z := by simp [cylPoint]

theorem cyl_norm (r θ z : ℝ) : ‖cylPoint r θ z‖ ≤ 2 * |r| + |z| := by
  unfold cylPoint
  refine (norm_add₃_le ..).trans ?_
  simp only [PiLp.norm_single, Real.norm_eq_abs, abs_mul]
  nlinarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ, abs_nonneg r, abs_nonneg (Real.cos θ),
    abs_nonneg (Real.sin θ)]

theorem cyl_mem {r θ z R : ℝ} (h : 2 * |r| + |z| ≤ R) : cylPoint r θ z ∈ Metric.closedBall (0 : Space) R := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (cyl_norm r θ z).trans h

theorem per_angle {u : ℝ → ℂ} (hu : Function.Periodic u (2 * Real.pi)) {a b : ℝ}
    (h : (a : Real.Angle) = b) : u a = u b := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
  have e : a = b + k * (2 * Real.pi) := by linear_combination hk
  rw [e]
  exact hu.int_mul k b

theorem w_circle {u : ℝ → ℂ} (hu : Function.Periodic u (2 * Real.pi)) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    u (Complex.arg (plane (cylPoint r θ z))) = u θ := by
  rw [plane_cyl, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr, ← self_sub_toIocDiv_zsmul]
  exact hu.sub_zsmul_eq _

theorem deriv_periodic {u : ℝ → ℂ} (hu : Function.Periodic u (2 * Real.pi)) :
    Function.Periodic (deriv u) (2 * Real.pi) := by
  intro x
  have h := deriv_comp_add_const (f := u) (a := 2 * Real.pi) (x := x)
  rw [show (fun x => u (x + 2 * Real.pi)) = u from funext hu] at h
  exact h.symm

theorem argw_cdAt {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u (2 * Real.pi)) {ζ : ℂ}
    (hζ : ζ ≠ 0) : ContDiffAt ℝ ∞ (fun ξ : ℂ => u (Complex.arg ξ)) ζ := by
  have hs : ∀ {ξ : ℂ}, ξ ∈ Complex.slitPlane → ContDiffAt ℝ ∞ (fun ξ : ℂ => Complex.arg ξ) ξ := by
    intro ξ h
    have h1 : ContDiffAt ℝ ∞ Complex.log ξ := (Complex.contDiffAt_log h).restrict_scalars ℝ
    have h2 := Complex.imCLM.contDiff.contDiffAt.comp ξ h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.log_im]
  by_cases h : ζ ∈ Complex.slitPlane
  · exact hu.contDiffAt.comp ζ (hs h)
  · have hn : -ζ ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at h ⊢
      push Not at h
      have hre : ζ.re ≠ 0 := fun h0 => hζ (Complex.ext h0 h.2)
      left
      simp only [Complex.neg_re]
      exact neg_pos.2 (lt_of_le_of_ne h.1 hre)
    have hc : ContDiffAt ℝ ∞ (fun ξ : ℂ => u (Complex.arg (-ξ) + Real.pi)) ζ :=
      hu.contDiffAt.comp ζ (((hs hn).comp ζ contDiff_neg.contDiffAt).add contDiffAt_const)
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hζ] with ξ hξ
    apply per_angle hp
    rw [Real.Angle.coe_add, Complex.arg_neg_coe_angle hξ, add_assoc, Real.Angle.coe_pi_add_coe_pi,
      add_zero]

def probe (χ : ℝ × ℝ → ℝ) (w : ℝ → ℂ) (y : Space) : ℂ :=
  (χ (cylRadius y, y 2) : ℂ) * w (Complex.arg (plane y))

theorem probe_cd {χ : ℝ × ℝ → ℝ} {w : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hpos : ∀ p ∈ tsupport χ, 0 < p.1)
    (hw : ContDiff ℝ ∞ w) (hp : Function.Periodic w (2 * Real.pi)) : ContDiff ℝ ∞ (probe χ w) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  rcases (Real.sqrt_nonneg _ : 0 ≤ cylRadius y).lt_or_eq with hy | hy
  · have h1 : ContDiffAt ℝ ∞ (fun y : Space => (cylRadius y, y 2)) y :=
      (radius_cdAt hy).prodMk (coord_cd 2).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun y : Space => (χ (cylRadius y, y 2) : ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (hχ.contDiffAt.comp y h1)
    have hne : plane y ≠ 0 := by
      intro h0
      have e0 : y 0 = 0 := by simpa [plane] using congrArg Complex.re h0
      have e1 : y 1 = 0 := by simpa [plane] using congrArg Complex.im h0
      simp [e0, e1] at hy
    have h3 : ContDiffAt ℝ ∞ (fun y : Space => w (Complex.arg (plane y))) y :=
      (argw_cdAt hw hp hne).comp y plane_cd.contDiffAt
    exact h2.mul h3
  · have hnot : (cylRadius y, y 2) ∉ tsupport χ := fun h => by
      have h1 := hpos _ h
      have h0 : cylRadius y = 0 := hy.symm
      simp only at h1
      linarith
    have hc : Continuous (fun y : Space => (cylRadius y, y 2)) :=
      radius_cont.prodMk (coord_cd 2).continuous
    have hev : probe χ w =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds ((isClosed_tsupport χ).isOpen_compl.mem_nhds hnot)]
        with x hx
      simp [probe, image_eq_zero_of_notMem_tsupport hx]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem abs_coord_le (y : Space) (i : Fin 3) (hi : i ≠ 2) : |y i| ≤ cylRadius y := by
  unfold cylRadius
  apply Real.abs_le_sqrt
  fin_cases i <;> simp at hi ⊢ <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]

theorem norm_le_coords (y : Space) : ‖y‖ ≤ |y 0| + |y 1| + |y 2| := by
  have h : y = ∑ j : Fin 3, y j • unitVector j := by
    ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]
  conv_lhs => rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [Fin.sum_univ_three, norm_smul, unitVector]

theorem probe_csupp {χ : ℝ × ℝ → ℝ} (w : ℝ → ℂ) (hc : HasCompactSupport χ) : HasCompactSupport (probe χ w) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (3 * R)) fun y hy => ?_
  by_contra hne
  have hχ : χ (cylRadius y, y 2) ≠ 0 := by
    intro h0; apply hne; simp [probe, h0]
  have hb := hR _ (subset_tsupport _ hχ)
  have h1 : |cylRadius y| ≤ R := by
    have := (norm_fst_le (cylRadius y, y 2)).trans hb; simpa [Real.norm_eq_abs] using this
  have h2 : |y 2| ≤ R := by
    have := (norm_snd_le (cylRadius y, y 2)).trans hb; simpa [Real.norm_eq_abs] using this
  have a0 := abs_coord_le y 0 (by decide)
  have a1 := abs_coord_le y 1 (by decide)
  have hr : cylRadius y ≤ |cylRadius y| := le_abs_self _
  apply hy
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_coords y).trans (by linarith)

theorem probe_cyl {χ : ℝ × ℝ → ℝ} {w : ℝ → ℂ} (hp : Function.Periodic w (2 * Real.pi)) {r : ℝ} (hr : 0 < r)
    (t z : ℝ) : probe χ w (cylPoint r t z) = (χ (r, z) : ℂ) * w t := by
  simp only [probe, radius_cyl hr, height_cyl, w_circle hp hr]

theorem curve_deriv (r z θ : ℝ) : HasDerivAt (fun t => cylPoint r t z) (turn (cylPoint r θ z)) θ := by
  have e : (fun t => cylPoint r t z) = fun t =>
      (r * Real.cos t) • unitVector 0 + (r * Real.sin t) • unitVector 1 + z • unitVector 2 := by
    funext t; simp only [cylPoint, single_eq]
  have e2 : turn (cylPoint r θ z) = (r * -Real.sin θ) • unitVector 0 + (r * Real.cos θ) • unitVector 1 +
      (0 : ℝ) • unitVector 2 := by
    ext i; fin_cases i <;> simp [turn, cylPoint, unitVector]
  rw [e, e2]
  exact ((((Real.hasDerivAt_cos θ).const_mul r).smul_const _).add
    (((Real.hasDerivAt_sin θ).const_mul r).smul_const _)).add ((hasDerivAt_const θ z).smul_const _)

theorem probe_turn {χ : ℝ × ℝ → ℝ} {w : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ (probe χ w)) (hw : ContDiff ℝ ∞ w)
    (hp : Function.Periodic w (2 * Real.pi)) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    fderiv ℝ (probe χ w) (cylPoint r θ z) (turn (cylPoint r θ z)) = (χ (r, z) : ℂ) * deriv w θ := by
  have hd : HasDerivAt (fun t => probe χ w (cylPoint r t z))
      (fderiv ℝ (probe χ w) (cylPoint r θ z) (turn (cylPoint r θ z))) θ :=
    ((hΦ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt θ (curve_deriv r z θ)
  have e : (fun t => probe χ w (cylPoint r t z)) = fun t => (χ (r, z) : ℂ) * w t :=
    funext fun t => probe_cyl hp hr t z
  rw [e] at hd
  exact hd.unique (((hw.differentiable (by simp)) θ).hasDerivAt.const_mul _)

theorem csupp_fderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : Space → F}
    (h : HasCompactSupport Φ) (v : Space → Space) : HasCompactSupport (fun y => fderiv ℝ Φ y (v y)) :=
  (h.fderiv (𝕜 := ℝ)).mono (fun y hy => by
    rw [Function.mem_support] at hy ⊢; intro h0; apply hy; simp [h0])

theorem loc_inner {g : Space → Space} (hg : LocallyIntegrable g volume) (c : Space) :
    LocallyIntegrable (fun y => inner ℝ (g y) c) volume :=
  locallyIntegrable_iff.2 fun _ hK => (hg.integrableOn_isCompact hK).inner_const c

theorem loc_turn {g : Space → Space} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun y => inner ℝ (g y) (turn y)) volume := by
  have e : (fun y => inner ℝ (g y) (turn y)) = fun y =>
      inner ℝ (g y) (unitVector 0) * (-(y 1)) + inner ℝ (g y) (unitVector 1) * y 0 :=
    funext fun y => by rw [turn_eq, inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
  rw [e]
  exact ((loc_inner hg _).mul_continuous (coord_cd 1).continuous.neg).add
    ((loc_inner hg _).mul_continuous (coord_cd 0).continuous)

theorem weak_turn_real (f : Space → ℝ) (g : Space → Space) (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume)
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * f y = -∫ y, φ y * inner ℝ (g y) (unitVector j))
    (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ y, fderiv ℝ φ y (turn y) * f y) + ∫ y, φ y * inner ℝ (g y) (turn y) = 0 := by
  have hd : ∀ i : Fin 3, ∀ y v, fderiv ℝ (fun y : Space => y i * φ y) y v = v i * φ y + y i * fderiv ℝ φ y v := by
    intro i y v
    have h : HasFDerivAt (fun y : Space => y i * φ y)
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ) y • fderiv ℝ φ y + φ y • (EuclideanSpace.proj i : Space →L[ℝ] ℝ)) y :=
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.mul ((hφ.differentiable (by simp)) y).hasFDerivAt
    rw [h.fderiv]
    simp
    ring
  have ht : ∀ i : Fin 3, IsTestScalar (fun y : Space => y i * φ y) :=
    fun i => ⟨(coord_cd i).mul hφ, hφc.mul_left⟩
  have E0 := hw _ (ht 1) 0
  have E1 := hw _ (ht 0) 1
  have u01 : (unitVector 0 : Space) 1 = 0 := by simp [unitVector]
  have u10 : (unitVector 1 : Space) 0 = 0 := by simp [unitVector]
  simp only [hd, u01, u10, zero_mul, zero_add] at E0 E1
  have cA : ∀ i j : Fin 3, Continuous (fun y : Space => y i * fderiv ℝ φ y (unitVector j)) :=
    fun i j => (coord_cd i).continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have sA : ∀ i j : Fin 3, HasCompactSupport (fun y : Space => y i * fderiv ℝ φ y (unitVector j)) :=
    fun i j => (csupp_fderiv_apply hφc (fun _ => unitVector j)).mul_left
  have cB : ∀ i : Fin 3, Continuous (fun y : Space => y i * φ y) :=
    fun i => (coord_cd i).continuous.mul hφ.continuous
  have A0 : Integrable (fun y => y 1 * fderiv ℝ φ y (unitVector 0) * f y) :=
    hf.integrable_smul_left_of_hasCompactSupport (cA 1 0) (sA 1 0)
  have A1 : Integrable (fun y => y 0 * fderiv ℝ φ y (unitVector 1) * f y) :=
    hf.integrable_smul_left_of_hasCompactSupport (cA 0 1) (sA 0 1)
  have B0 : Integrable (fun y => y 1 * φ y * inner ℝ (g y) (unitVector 0)) :=
    (loc_inner hg _).integrable_smul_left_of_hasCompactSupport (cB 1) (ht 1).2
  have B1 : Integrable (fun y => y 0 * φ y * inner ℝ (g y) (unitVector 1)) :=
    (loc_inner hg _).integrable_smul_left_of_hasCompactSupport (cB 0) (ht 0).2
  have e1 : (fun y => fderiv ℝ φ y (turn y) * f y) = fun y =>
      y 0 * fderiv ℝ φ y (unitVector 1) * f y - y 1 * fderiv ℝ φ y (unitVector 0) * f y := by
    funext y; rw [turn_eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
  have e2 : (fun y => φ y * inner ℝ (g y) (turn y)) = fun y =>
      y 0 * φ y * inner ℝ (g y) (unitVector 1) - y 1 * φ y * inner ℝ (g y) (unitVector 0) := by
    funext y; rw [turn_eq, inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
  rw [e1, e2, integral_sub A1 A0, integral_sub B1 B0, E0, E1]
  ring

theorem re_int {F : Space → ℂ} (hF : Integrable F) : (∫ y, F y).re = ∫ y, (F y).re := by
  have := integral_re hF
  simp only [RCLike.re_to_complex] at this
  exact this.symm

theorem im_int {F : Space → ℂ} (hF : Integrable F) : (∫ y, F y).im = ∫ y, (F y).im := by
  have := integral_im hF
  simp only [RCLike.im_to_complex] at this
  exact this.symm

theorem weak_turn (f : Space → ℝ) (g : Space → Space) (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume)
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * f y = -∫ y, φ y * inner ℝ (g y) (unitVector j))
    (Φ : Space → ℂ) (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) :
    Integrable (fun y => fderiv ℝ Φ y (turn y) * (f y : ℂ)) ∧
      Integrable (fun y => Φ y * (inner ℝ (g y) (turn y) : ℂ)) ∧
      (∫ y, fderiv ℝ Φ y (turn y) * (f y : ℂ)) + ∫ y, Φ y * (inner ℝ (g y) (turn y) : ℂ) = 0 := by
  have hc : Continuous (fun y => fderiv ℝ Φ y (turn y)) :=
    (hΦ.continuous_fderiv (by simp)).clm_apply turn_cont
  have I1 : Integrable (fun y => fderiv ℝ Φ y (turn y) * (f y : ℂ)) := by
    refine (hf.integrable_smul_right_of_hasCompactSupport hc (csupp_fderiv_apply hΦc turn)).congr ?_
    filter_upwards with y
    rw [Complex.real_smul, mul_comm]
  have I2 : Integrable (fun y => Φ y * (inner ℝ (g y) (turn y) : ℂ)) := by
    refine ((loc_turn hg).integrable_smul_right_of_hasCompactSupport hΦ.continuous hΦc).congr ?_
    filter_upwards with y
    rw [Complex.real_smul, mul_comm]
  have hdiff := hΦ.differentiable (by simp)
  have fd_re : ∀ y v, fderiv ℝ (fun y => (Φ y).re) y v = (fderiv ℝ Φ y v).re := by
    intro y v
    have h : HasFDerivAt (fun y => (Φ y).re) (Complex.reCLM.comp (fderiv ℝ Φ y)) y :=
      Complex.reCLM.hasFDerivAt.comp y (hdiff y).hasFDerivAt
    rw [h.fderiv]; rfl
  have fd_im : ∀ y v, fderiv ℝ (fun y => (Φ y).im) y v = (fderiv ℝ Φ y v).im := by
    intro y v
    have h : HasFDerivAt (fun y => (Φ y).im) (Complex.imCLM.comp (fderiv ℝ Φ y)) y :=
      Complex.imCLM.hasFDerivAt.comp y (hdiff y).hasFDerivAt
    rw [h.fderiv]; rfl
  refine ⟨I1, I2, Complex.ext ?_ ?_⟩
  · have R := weak_turn_real f g hf hg hw (fun y => (Φ y).re) (Complex.reCLM.contDiff.comp hΦ)
      (hΦc.comp_left Complex.zero_re)
    rw [Complex.add_re, re_int I1, re_int I2, Complex.zero_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ← fd_re]
    exact R
  · have R := weak_turn_real f g hf hg hw (fun y => (Φ y).im) (Complex.imCLM.contDiff.comp hΦ)
      (hΦc.comp_left Complex.zero_im)
    rw [Complex.add_im, im_int I1, im_int I2, Complex.zero_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, ← fd_im]
    exact R

theorem cyl_exchange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {k : Space → E} (hk : Integrable k) :
    (∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 →
      IntervalIntegrable (fun θ => k (cylPoint q.1 θ q.2)) volume 0 (2 * Real.pi)) ∧
    IntegrableOn (fun q : ℝ × ℝ => q.1 • ∫ θ in (0 : ℝ)..(2 * Real.pi), k (cylPoint q.1 θ q.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  set gk : (ℝ × ℝ) × ℝ → E := fun w => k (toSpace w) with hgk
  have hg : Integrable gk := (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hk
  have hH : IntegrableOn (fun x : (ℝ × ℝ) × ℝ => x.1.1 • gk (cylMap.symm x)) cylMap.target := by
    have h1 : IntegrableOn gk (cylMap.symm '' cylMap.target) :=
      (integrableOn_univ.mpr hg).congr_set_ae image_ae
    rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume cylMap.open_target.measurableSet
        (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn gk] at h1
    refine h1.congr_fun (fun x hx => ?_) cylMap.open_target.measurableSet
    simp only [abs_det_eq hx]
  set H : (ℝ × ℝ) × ℝ → E := fun x => x.1.1 • gk (cylMap.symm x) with hH_def
  have hHσ : IntegrableOn (H ∘ swapEquiv)
      ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-Real.pi) Real.pi) := by
    rw [← swapEquiv_preimage]
    exact (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  have hP : Integrable (H ∘ swapEquiv) ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]; exact hHσ
  have hval : ∀ q : ℝ × ℝ, ∀ θ, (H ∘ swapEquiv) (q, θ) = q.1 • k (cylPoint q.1 θ q.2) := by
    intro q θ; obtain ⟨r, z⟩ := q
    simp only [Function.comp_apply, swapEquiv_apply, hH_def, hgk]
    rw [show cylPoint r θ z = toSpace ((r * Real.cos θ, r * Real.sin θ), z) from (toSpace_apply r θ z).symm]
    rfl
  have hper : ∀ q : ℝ × ℝ, Function.Periodic (fun θ => k (cylPoint q.1 θ q.2)) (2 * Real.pi) :=
    fun q θ => by simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hshift : ∀ q : ℝ × ℝ, ∫ θ in (0 : ℝ)..(2 * Real.pi), k (cylPoint q.1 θ q.2) =
      ∫ θ in Ioo (-Real.pi) Real.pi, k (cylPoint q.1 θ q.2) := by
    intro q
    have hsh := (hper q).intervalIntegral_add_eq 0 (-Real.pi)
    rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at hsh
    rw [hsh, intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo]
  refine ⟨?_, ?_⟩
  · have h1 := hP.prod_right_ae
    rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at h1
    filter_upwards [h1] with q hq hq1
    have hI : IntegrableOn (fun θ => k (cylPoint q.1 θ q.2)) (Ioo (-Real.pi) Real.pi) := by
      refine ((hq ⟨hq1, mem_univ _⟩).smul q.1⁻¹).congr (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Pi.smul_apply, hval, smul_smul, inv_mul_cancel₀ hq1.ne', one_smul]
    have hII : IntervalIntegrable (fun θ => k (cylPoint q.1 θ q.2)) volume (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hpi).2 hI
    exact (hper q).intervalIntegrable Real.two_pi_pos.ne' hII 0 (2 * Real.pi)
  · have h2 := hP.integral_prod_left
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [hval]
    rw [integral_smul, hshift]

theorem sections {k : Space → ℝ} (hk : LocallyIntegrable k volume) :
    ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 →
      IntervalIntegrable (fun θ => k (cylPoint q.1 θ q.2)) volume 0 (2 * Real.pi) := by
  have hn : ∀ n : ℕ, ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 → IntervalIntegrable
      (fun θ => (Metric.closedBall (0 : Space) n).indicator k (cylPoint q.1 θ q.2)) volume 0 (2 * Real.pi) :=
    fun n => (cyl_exchange ((integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (hk.integrableOn_isCompact (isCompact_closedBall _ _)))).1
  filter_upwards [ae_all_iff.2 hn] with q hq hq1
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * |q.1| + |q.2|)
  have e : (fun θ => (Metric.closedBall (0 : Space) n).indicator k (cylPoint q.1 θ q.2)) =
      fun θ => k (cylPoint q.1 θ q.2) := by
    funext θ; exact indicator_of_mem (cyl_mem hn) _
  rw [← e]; exact hq n hq1

theorem bdd_of {u : ℝ → ℂ} (hu : Continuous u) : ∃ C, ∀ y : Space, ‖u (Complex.arg (plane y))‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -Real.pi) (b := Real.pi)).exists_bound_of_continuousOn hu.continuousOn
  exact ⟨C, fun y => hC _ ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩⟩

theorem meas_of {u : ℝ → ℂ} (hu : Continuous u) {μ : Measure Space} :
    AEStronglyMeasurable (fun y => u (Complex.arg (plane y))) μ :=
  (hu.measurable.comp (Complex.measurable_arg.comp plane_cd.continuous.measurable)).aestronglyMeasurable

def kern (w : ℝ → ℂ) (f : Space → ℝ) (g : Space → Space) (y : Space) : ℂ :=
  deriv w (Complex.arg (plane y)) * (f y : ℂ) + w (Complex.arg (plane y)) * (inner ℝ (g y) (turn y) : ℂ)

theorem kern_int {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) {f : Space → ℝ} {g : Space → Space}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) (R : ℝ) :
    IntegrableOn (kern w f g) (Metric.closedBall 0 R) := by
  have hB : IsCompact (Metric.closedBall (0 : Space) R) := isCompact_closedBall _ _
  obtain ⟨C1, hC1⟩ := bdd_of (hw.continuous_deriv (by simp))
  obtain ⟨C2, hC2⟩ := bdd_of hw.continuous
  exact (((hf.integrableOn_isCompact hB).ofReal).bdd_mul (meas_of (hw.continuous_deriv (by simp)))
      (Filter.Eventually.of_forall hC1)).add
    ((((loc_turn hg).integrableOn_isCompact hB).ofReal).bdd_mul (meas_of hw.continuous)
      (Filter.Eventually.of_forall hC2))

theorem kern_cyl {w : ℝ → ℂ} (hp : Function.Periodic w (2 * Real.pi)) (f : Space → ℝ) (g : Space → Space)
    {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    kern w f g (cylPoint r θ z) = deriv w θ * (f (cylPoint r θ z) : ℂ) +
      w θ * ((r * inner ℝ (g (cylPoint r θ z)) (angularUnit θ) : ℝ) : ℂ) := by
  simp only [kern, w_circle hp hr, w_circle (deriv_periodic hp) hr, turn_cyl, real_inner_smul_right]

end Internal.CircleWeak

open Internal.CircleWeak in
theorem circleWeak : CircleWeakStatement := by
  intro f g hf hg hw
  have S : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      IntervalIntegrable (fun θ => f (cylPoint p.1 θ p.2)) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (fun θ => inner ℝ (g (cylPoint p.1 θ p.2)) (angularUnit θ)) volume 0
        (2 * Real.pi) := by
    filter_upwards [sections hf, sections (loc_turn hg)] with p h1 h2 hp
    refine ⟨h1 hp, (intervalIntegrable_congr fun θ _ => ?_).1 ((h2 hp).const_mul p.1⁻¹)⟩
    simp only [turn_cyl, real_inner_smul_right]
    field_simp
  refine ⟨S, fun w hwc hwp => ?_⟩
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hLoc : LocallyIntegrableOn (fun q : ℝ × ℝ => q.1 • ∫ θ in (0 : ℝ)..(2 * Real.pi),
      kern w f g (cylPoint q.1 θ q.2)) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hKc
    obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
    have hI := (cyl_exchange ((integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (kern_int hwc hf hg (3 * R)))).2
    refine (hI.mono_set hKU).congr_fun (fun q hq => ?_) hKc.measurableSet
    have hq' := hR q hq
    have h1 : |q.1| ≤ R := by
      have := (norm_fst_le q).trans hq'; simpa [Real.norm_eq_abs] using this
    have h2 : |q.2| ≤ R := by
      have := (norm_snd_le q).trans hq'; simpa [Real.norm_eq_abs] using this
    have hb : 2 * |q.1| + |q.2| ≤ 3 * R := by linarith
    simp only
    congr 1
    exact intervalIntegral.integral_congr fun θ _ => indicator_of_mem (cyl_mem hb) _
  have hZ := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLoc ?_
  · filter_upwards [hZ, S] with p hp hS hp1
    have h0 := hp ⟨hp1, mem_univ _⟩
    have h0' : ∫ θ in (0 : ℝ)..(2 * Real.pi), kern w f g (cylPoint p.1 θ p.2) = 0 :=
      (smul_eq_zero.1 h0).resolve_left hp1.ne'
    rw [intervalIntegral.integral_congr (fun θ _ => kern_cyl hwp f g hp1 θ p.2)] at h0'
    have ia : IntervalIntegrable (fun θ => deriv w θ * (f (cylPoint p.1 θ p.2) : ℂ)) volume 0 (2 * Real.pi) :=
      (show IntervalIntegrable (fun θ => (f (cylPoint p.1 θ p.2) : ℂ)) volume 0 (2 * Real.pi) from
        ⟨(hS hp1).1.1.ofReal, (hS hp1).1.2.ofReal⟩).continuousOn_mul
        (hwc.continuous_deriv (by simp)).continuousOn
    have ib' := ((hS hp1).2.const_mul p.1)
    have ib : IntervalIntegrable (fun θ => w θ *
        ((p.1 * inner ℝ (g (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
      (show IntervalIntegrable (fun θ => ((p.1 * inner ℝ (g (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ))
        volume 0 (2 * Real.pi) from ⟨ib'.1.ofReal, ib'.2.ofReal⟩).continuousOn_mul hwc.continuous.continuousOn
    rw [intervalIntegral.integral_add ia ib] at h0'
    linear_combination h0'
  · intro χ hχ hχc hsub
    have hpos : ∀ p ∈ tsupport χ, 0 < p.1 := fun p hp => (hsub hp).1
    have hΦ := probe_cd hχ hpos hwc hwp
    obtain ⟨I1, I2, E⟩ := weak_turn f g hf hg hw (probe χ w) hΦ (probe_csupp w hχc)
    have E' : ∫ y, (fderiv ℝ (probe χ w) y (turn y) * (f y : ℂ) +
        probe χ w y * (inner ℝ (g y) (turn y) : ℂ)) = 0 := by
      rw [integral_add I1 I2]; exact E
    rw [CellFormula.cylChange (fun y => fderiv ℝ (probe χ w) y (turn y) * (f y : ℂ) +
        probe χ w y * (inner ℝ (g y) (turn y) : ℂ)) (I1.add I2)] at E'
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))]
    · rw [← E']
      refine setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun q hq => ?_
      have hq1 : 0 < q.1 := hq.1
      have ept : ∀ θ, fderiv ℝ (probe χ w) (cylPoint q.1 θ q.2) (turn (cylPoint q.1 θ q.2)) *
            (f (cylPoint q.1 θ q.2) : ℂ) + probe χ w (cylPoint q.1 θ q.2) *
            (inner ℝ (g (cylPoint q.1 θ q.2)) (turn (cylPoint q.1 θ q.2)) : ℂ) =
          (χ q : ℂ) * kern w f g (cylPoint q.1 θ q.2) := by
        intro θ
        rw [probe_turn hΦ hwc hwp hq1, probe_cyl hwp hq1, kern, w_circle hwp hq1,
          w_circle (deriv_periodic hwp) hq1, Prod.mk.eta]
        ring
      simp only [ept, intervalIntegral.integral_const_mul, Complex.real_smul]
      ring
    · intro q hq
      have : χ q = 0 := image_eq_zero_of_notMem_tsupport (fun h => hq (hsub h))
      simp [this]

end Breakdown.CellCert.CellEnergy
