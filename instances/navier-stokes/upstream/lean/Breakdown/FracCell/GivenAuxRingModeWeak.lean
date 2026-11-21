import Breakdown.FracCell.GivenAuxInverseSquareRing
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory Set Filter
open scoped ContDiff Pointwise Topology

noncomputable section

namespace Breakdown.FracInternal.RingModeWeak

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.SteadyCert
open Breakdown.CellCert.CellEnergy.Internal.CircleWeak

def wave (m : ℤ) (θ : ℝ) : ℂ := Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I)

theorem wave_deriv (m : ℤ) (θ : ℝ) : HasDerivAt (wave m) ((m : ℂ) * Complex.I * wave m θ) θ := by
  unfold wave
  have h : HasDerivAt (fun θ : ℝ => (m : ℂ) * (θ : ℂ) * Complex.I) ((m : ℂ) * ((1 : ℝ) : ℂ) * Complex.I) θ :=
    (((hasDerivAt_id θ).ofReal_comp).const_mul (m : ℂ)).mul_const Complex.I
  convert h.cexp using 1
  push_cast
  ring

theorem wave_cd (m : ℤ) : ContDiff ℝ ∞ (wave m) := by
  unfold wave
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const).cexp

theorem wave_per (m : ℤ) : Function.Periodic (wave m) (2 * Real.pi) := by
  intro θ
  unfold wave
  rw [show (m : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
      (m : ℂ) * (θ : ℂ) * Complex.I + (m : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem wave_mul (a b : ℤ) (θ : ℝ) : wave a θ * wave b θ = wave (a + b) θ := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem wave_one (θ : ℝ) : wave 1 θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  unfold wave
  rw [show ((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I = (θ : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
  push_cast
  ring

theorem wave_neg_one (θ : ℝ) : wave (-1) θ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  unfold wave
  rw [show ((-1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

def cp (χ : ℝ × ℝ → ℂ) (m : ℤ) (y : Space) : ℂ := χ (cylRadius y, y 2) * wave m (Complex.arg (plane y))

def Good (χ : ℝ × ℝ → ℂ) : Prop := ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ ∀ p ∈ tsupport χ, 0 < p.1

theorem pair_cont : Continuous (fun y : Space => (cylRadius y, y 2)) :=
  radius_cont.prodMk (coord_cd 2).continuous

theorem cp_near_zero {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) {y : Space} (hy : ¬ 0 < cylRadius y) :
    cp χ m =ᶠ[𝓝 y] fun _ => 0 := by
  have hnot : (cylRadius y, y 2) ∉ tsupport χ := fun h => hy (hχ.2.2 _ h)
  filter_upwards [pair_cont.continuousAt.preimage_mem_nhds ((isClosed_tsupport χ).isOpen_compl.mem_nhds hnot)]
    with x hx
  simp [cp, image_eq_zero_of_notMem_tsupport hx]

theorem cp_cd {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) : ContDiff ℝ ∞ (cp χ m) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : 0 < cylRadius y
  · have h1 : ContDiffAt ℝ ∞ (fun y : Space => (cylRadius y, y 2)) y :=
      (radius_cdAt hy).prodMk (coord_cd 2).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun y : Space => χ (cylRadius y, y 2)) y :=
      hχ.1.contDiffAt.comp y h1
    have hne : plane y ≠ 0 := by
      intro h0
      have e0 : y 0 = 0 := by simpa [plane] using congrArg Complex.re h0
      have e1 : y 1 = 0 := by simpa [plane] using congrArg Complex.im h0
      simp [cylRadius, e0, e1] at hy
    have h3 : ContDiffAt ℝ ∞ (fun y : Space => wave m (Complex.arg (plane y))) y :=
      (argw_cdAt (wave_cd m) (wave_per m) hne).comp y plane_cd.contDiffAt
    exact h2.mul h3
  · exact contDiffAt_const.congr_of_eventuallyEq (cp_near_zero hχ m hy)

theorem cp_csupp {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) : HasCompactSupport (cp χ m) := by
  obtain ⟨R, hR⟩ := hχ.2.1.isCompact.isBounded.exists_norm_le
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (3 * R)) fun y hy => ?_
  by_contra hne
  have hχ0 : χ (cylRadius y, y 2) ≠ 0 := by
    intro h0; apply hne; simp [cp, h0]
  have hb := hR _ (subset_tsupport _ hχ0)
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

theorem cp_cyl (χ : ℝ × ℝ → ℂ) (m : ℤ) {r : ℝ} (hr : 0 < r) (t z : ℝ) :
    cp χ m (cylPoint r t z) = χ (r, z) * wave m t := by
  simp only [cp, radius_cyl hr, height_cyl, w_circle (wave_per m) hr]

theorem cyl_self {y : Space} (hy : 0 < cylRadius y) :
    cylPoint (cylRadius y) (Complex.arg (plane y)) (y 2) = y := by
  have hn : ‖plane y‖ = cylRadius y := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [plane, cylRadius, sq]
  have hc : cylRadius y * Real.cos (Complex.arg (plane y)) = y 0 := by
    rw [← hn]; simpa [plane] using Complex.norm_mul_cos_arg (plane y)
  have hs : cylRadius y * Real.sin (Complex.arg (plane y)) = y 1 := by
    rw [← hn]; simpa [plane] using Complex.norm_mul_sin_arg (plane y)
  ext i
  fin_cases i
  · simp [cylPoint, hc]
  · simp [cylPoint, hs]
  · simp [cylPoint]


theorem cp_zero {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) {y : Space} (hy : ¬ 0 < cylRadius y) : cp χ m y = 0 :=
  (cp_near_zero hχ m hy).self_of_nhds

theorem cp_fderiv_zero {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) {y : Space} (hy : ¬ 0 < cylRadius y) :
    fderiv ℝ (cp χ m) y = 0 := by
  rw [(cp_near_zero hχ m hy).fderiv_eq, fderiv_const_apply]

theorem good_of {χ F : ℝ × ℝ → ℂ} (hχ : Good χ) (hz : ∀ p, p ∉ tsupport χ → F =ᶠ[𝓝 p] fun _ => 0)
    (hcd : ∀ p ∈ tsupport χ, ContDiffAt ℝ ∞ F p) : Good F := by
  have hsub : Function.support F ⊆ tsupport χ := by
    intro p hp
    by_contra h
    exact hp (hz p h).self_of_nhds
  have hts : tsupport F ⊆ tsupport χ := closure_minimal hsub (isClosed_tsupport χ)
  refine ⟨contDiff_iff_contDiffAt.2 fun p => ?_, hχ.2.1.mono' hsub, fun p hp => hχ.2.2 p (hts hp)⟩
  by_cases hp : p ∈ tsupport χ
  · exact hcd p hp
  · exact contDiffAt_const.congr_of_eventuallyEq (hz p hp)

theorem near_zero_of {χ : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (hp : p ∉ tsupport χ) :
    ∀ᶠ q in 𝓝 p, q ∉ tsupport χ :=
  (isClosed_tsupport χ).isOpen_compl.mem_nhds hp

def plusF (χ : ℝ × ℝ → ℂ) (m : ℤ) (p : ℝ × ℝ) : ℂ := fderiv ℝ χ p (1, 0) - (m : ℂ) * (p.1⁻¹ • χ p)

def minusF (χ : ℝ × ℝ → ℂ) (m : ℤ) (p : ℝ × ℝ) : ℂ := fderiv ℝ χ p (1, 0) + (m : ℂ) * (p.1⁻¹ • χ p)

def heightF (χ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ χ p (0, 1)

theorem fd_cd {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (v : ℝ × ℝ) : ContDiff ℝ ∞ (fun p => fderiv ℝ χ p v) :=
  (hχ.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem quot_cdAt {χ : ℝ × ℝ → ℂ} (hχ : Good χ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => q.1⁻¹ • χ q) p :=
  ((contDiffAt_inv ℝ hp.ne').comp p contDiffAt_fst).smul hχ.1.contDiffAt

theorem good_plus {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) : Good (plusF χ m) := by
  refine good_of hχ (fun p hp => ?_) (fun p hp => ?_)
  · filter_upwards [near_zero_of hp] with q hq
    simp [plusF, fderiv_of_notMem_tsupport ℝ hq, image_eq_zero_of_notMem_tsupport hq]
  · exact (fd_cd hχ _).contDiffAt.sub (contDiffAt_const.mul (quot_cdAt hχ (hχ.2.2 p hp)))

theorem good_minus {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) : Good (minusF χ m) := by
  refine good_of hχ (fun p hp => ?_) (fun p hp => ?_)
  · filter_upwards [near_zero_of hp] with q hq
    simp [minusF, fderiv_of_notMem_tsupport ℝ hq, image_eq_zero_of_notMem_tsupport hq]
  · exact (fd_cd hχ _).contDiffAt.add (contDiffAt_const.mul (quot_cdAt hχ (hχ.2.2 p hp)))

theorem good_height {χ : ℝ × ℝ → ℂ} (hχ : Good χ) : Good (heightF χ) := by
  refine good_of hχ (fun p hp => ?_) (fun p _ => (fd_cd hχ _).contDiffAt)
  filter_upwards [near_zero_of hp] with q hq
  simp [heightF, fderiv_of_notMem_tsupport ℝ hq]

theorem good_add {χ ψ : ℝ × ℝ → ℂ} (hχ : Good χ) (hψ : Good ψ) : Good (fun p => χ p + ψ p) := by
  refine ⟨hχ.1.add hψ.1, hχ.2.1.add hψ.2.1, fun p hp => ?_⟩
  rcases (tsupport_add χ ψ) hp with h | h
  · exact hχ.2.2 p h
  · exact hψ.2.2 p h

theorem good_smul {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (c : ℂ) : Good (fun p => c * χ p) :=
  ⟨contDiff_const.mul hχ.1, hχ.2.1.mul_left, fun p hp => hχ.2.2 p (tsupport_mul_subset_right hp)⟩

theorem cyl_radial (s θ z : ℝ) : cylPoint s θ z = s • radialUnit θ + EuclideanSpace.single 2 z := by
  ext i; fin_cases i <;> simp [cylPoint, radialUnit]

theorem cyl_height (r θ s : ℝ) : cylPoint r θ s = cylPoint r θ 0 + s • unitVector 2 := by
  ext i; fin_cases i <;> simp [cylPoint, unitVector]

theorem e0_eq (θ : ℝ) : unitVector 0 = Real.cos θ • radialUnit θ - Real.sin θ • angularUnit θ := by
  ext i; fin_cases i <;> simp [unitVector, radialUnit, angularUnit] <;> nlinarith [Real.cos_sq_add_sin_sq θ]

theorem e1_eq (θ : ℝ) : unitVector 1 = Real.sin θ • radialUnit θ + Real.cos θ • angularUnit θ := by
  ext i; fin_cases i <;> simp [unitVector, radialUnit, angularUnit] <;> nlinarith [Real.cos_sq_add_sin_sq θ]

theorem d_rad {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    fderiv ℝ (cp χ m) (cylPoint r θ z) (radialUnit θ) = fderiv ℝ χ (r, z) (1, 0) * wave m θ := by
  have hd := (cp_cd hχ m).differentiable (by simp)
  have hc : HasDerivAt (fun s => cylPoint s θ z) (radialUnit θ) r := by
    have h0 : HasDerivAt (fun s : ℝ => s • radialUnit θ + EuclideanSpace.single 2 z) ((1 : ℝ) • radialUnit θ) r :=
      ((hasDerivAt_id r).smul_const (radialUnit θ)).add_const _
    rw [one_smul] at h0
    exact h0.congr_of_eventuallyEq (Eventually.of_forall fun s => cyl_radial s θ z)
  have h1 : HasDerivAt (fun s => cp χ m (cylPoint s θ z))
      (fderiv ℝ (cp χ m) (cylPoint r θ z) (radialUnit θ)) r :=
    (hd _).hasFDerivAt.comp_hasDerivAt r hc
  have hp : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℝ)) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r z)
  have h2 : HasDerivAt (fun s => χ (s, z) * wave m θ) (fderiv ℝ χ (r, z) (1, 0) * wave m θ) r :=
    (((hχ.1.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt r hp).mul_const _
  have h3 : (fun s => cp χ m (cylPoint s θ z)) =ᶠ[𝓝 r] fun s => χ (s, z) * wave m θ := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact cp_cyl χ m hs θ z
  exact h1.unique (h2.congr_of_eventuallyEq h3)

theorem d_height {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    fderiv ℝ (cp χ m) (cylPoint r θ z) (unitVector 2) = fderiv ℝ χ (r, z) (0, 1) * wave m θ := by
  have hd := (cp_cd hχ m).differentiable (by simp)
  have hc : HasDerivAt (fun s => cylPoint r θ s) (unitVector 2) z := by
    have h0 : HasDerivAt (fun s : ℝ => cylPoint r θ 0 + s • unitVector 2) ((1 : ℝ) • unitVector 2) z :=
      ((hasDerivAt_id z).smul_const (unitVector 2)).const_add _
    rw [one_smul] at h0
    exact h0.congr_of_eventuallyEq (Eventually.of_forall fun s => cyl_height r θ s)
  have h1 : HasDerivAt (fun s => cp χ m (cylPoint r θ s))
      (fderiv ℝ (cp χ m) (cylPoint r θ z) (unitVector 2)) z :=
    (hd _).hasFDerivAt.comp_hasDerivAt z hc
  have hp : HasDerivAt (fun s : ℝ => (r, s)) ((0 : ℝ), (1 : ℝ)) z :=
    (hasDerivAt_const z r).prodMk (hasDerivAt_id z)
  have h2 : HasDerivAt (fun s => χ (r, s) * wave m θ) (fderiv ℝ χ (r, z) (0, 1) * wave m θ) z :=
    (((hχ.1.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt z hp).mul_const _
  have h3 : (fun s => cp χ m (cylPoint r θ s)) = fun s => χ (r, s) * wave m θ :=
    funext fun s => cp_cyl χ m hr θ s
  rw [h3] at h1
  exact h1.unique h2

theorem d_ang {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    fderiv ℝ (cp χ m) (cylPoint r θ z) (angularUnit θ) =
      (r : ℂ)⁻¹ * (χ (r, z) * ((m : ℂ) * Complex.I * wave m θ)) := by
  have hd := (cp_cd hχ m).differentiable (by simp)
  have h1 : HasDerivAt (fun t => cp χ m (cylPoint r t z))
      (fderiv ℝ (cp χ m) (cylPoint r θ z) (turn (cylPoint r θ z))) θ :=
    (hd _).hasFDerivAt.comp_hasDerivAt θ (curve_deriv r z θ)
  have e : (fun t => cp χ m (cylPoint r t z)) = fun t => χ (r, z) * wave m t :=
    funext fun t => cp_cyl χ m hr t z
  rw [e] at h1
  have h2 := h1.unique ((wave_deriv m θ).const_mul (χ (r, z)))
  rw [turn_cyl, map_smul, Complex.real_smul] at h2
  rw [← h2, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hr.ne'), one_mul]

theorem plus_eq {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) :
    (fun y => fderiv ℝ (cp χ m) y (unitVector 0) + Complex.I * fderiv ℝ (cp χ m) y (unitVector 1)) =
      cp (plusF χ m) (m + 1) := by
  funext y
  by_cases hy : 0 < cylRadius y
  · have key : ∀ r θ z : ℝ, 0 < r → fderiv ℝ (cp χ m) (cylPoint r θ z) (unitVector 0) +
        Complex.I * fderiv ℝ (cp χ m) (cylPoint r θ z) (unitVector 1) = cp (plusF χ m) (m + 1) (cylPoint r θ z) := by
      intro r θ z hr
      rw [e0_eq θ, e1_eq θ, map_sub, map_add, map_smul, map_smul, map_smul, map_smul, d_rad hχ m hr,
        d_ang hχ m hr, cp_cyl _ _ hr, plusF, ← wave_mul, wave_one, Complex.real_smul, Complex.real_smul,
        Complex.real_smul, Complex.real_smul, Complex.real_smul]
      push_cast
      linear_combination (Complex.cos (θ : ℂ) * (χ (r, z) * (m : ℂ) * wave m θ * (r : ℂ)⁻¹)) * Complex.I_sq
    rw [← cyl_self hy]
    exact key _ _ _ hy
  · rw [cp_fderiv_zero hχ m hy, cp_zero (good_plus hχ m) _ hy]
    simp

theorem minus_eq {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) :
    (fun y => fderiv ℝ (cp χ m) y (unitVector 0) - Complex.I * fderiv ℝ (cp χ m) y (unitVector 1)) =
      cp (minusF χ m) (m - 1) := by
  funext y
  by_cases hy : 0 < cylRadius y
  · have key : ∀ r θ z : ℝ, 0 < r → fderiv ℝ (cp χ m) (cylPoint r θ z) (unitVector 0) -
        Complex.I * fderiv ℝ (cp χ m) (cylPoint r θ z) (unitVector 1) = cp (minusF χ m) (m - 1) (cylPoint r θ z) := by
      intro r θ z hr
      rw [e0_eq θ, e1_eq θ, map_sub, map_add, map_smul, map_smul, map_smul, map_smul, d_rad hχ m hr,
        d_ang hχ m hr, cp_cyl _ _ hr, minusF, sub_eq_add_neg m 1, ← wave_mul, wave_neg_one, Complex.real_smul,
        Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul]
      push_cast
      linear_combination (-(Complex.cos (θ : ℂ) * (χ (r, z) * (m : ℂ) * wave m θ * (r : ℂ)⁻¹))) * Complex.I_sq
    rw [← cyl_self hy]
    exact key _ _ _ hy
  · rw [cp_fderiv_zero hχ m hy, cp_zero (good_minus hχ m) _ hy]
    simp

theorem height_eq {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) :
    (fun y => fderiv ℝ (cp χ m) y (unitVector 2)) = cp (heightF χ) m := by
  funext y
  by_cases hy : 0 < cylRadius y
  · have key : ∀ r θ z : ℝ, 0 < r → fderiv ℝ (cp χ m) (cylPoint r θ z) (unitVector 2) =
        cp (heightF χ) m (cylPoint r θ z) := by
      intro r θ z hr
      rw [d_height hχ m hr, cp_cyl _ _ hr, heightF]
    rw [← cyl_self hy]
    exact key _ _ _ hy
  · rw [cp_fderiv_zero hχ m hy, cp_zero (good_height hχ) _ hy]
    simp

theorem cp_add (χ ψ : ℝ × ℝ → ℂ) (m : ℤ) (y : Space) : cp (fun p => χ p + ψ p) m y = cp χ m y + cp ψ m y := by
  simp only [cp]; ring

theorem cp_smul (χ : ℝ × ℝ → ℂ) (c : ℂ) (m : ℤ) (y : Space) : cp (fun p => c * χ p) m y = c * cp χ m y := by
  simp only [cp]; ring

theorem d0_cp {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) :
    (fun y => fderiv ℝ (cp χ m) y (unitVector 0)) =
      fun y => (1 / 2 : ℂ) * (1 * cp (plusF χ m) (m + 1) y + 1 * cp (minusF χ m) (m - 1) y) := by
  funext y
  have h1 := congrFun (plus_eq hχ m) y
  have h2 := congrFun (minus_eq hχ m) y
  try simp only at h1 h2
  rw [← h1, ← h2]; ring

theorem d1_cp {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) :
    (fun y => fderiv ℝ (cp χ m) y (unitVector 1)) =
      fun y => (-(Complex.I / 2)) * (1 * cp (plusF χ m) (m + 1) y + (-1) * cp (minusF χ m) (m - 1) y) := by
  funext y
  have h1 := congrFun (plus_eq hχ m) y
  have h2 := congrFun (minus_eq hχ m) y
  try simp only at h1 h2
  rw [← h1, ← h2]
  linear_combination (fderiv ℝ (cp χ m) y (unitVector 1)) * Complex.I_sq

theorem fd_comb {A B : Space → ℂ} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B) (c d e : ℂ) (y v : Space) :
    fderiv ℝ (fun x => c * (d * A x + e * B x)) y v = c * (d * fderiv ℝ A y v + e * fderiv ℝ B y v) := by
  have h : HasFDerivAt (fun x => c * (d * A x + e * B x)) (c • (d • fderiv ℝ A y + e • fderiv ℝ B y)) y :=
    (((hA y).hasFDerivAt.const_mul d).add ((hB y).hasFDerivAt.const_mul e)).const_mul c
  rw [h.fderiv]
  simp [smul_eq_mul]
  ring

theorem second {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (y v w : Space) :
    iteratedFDeriv ℝ 2 Φ y ![v, w] = fderiv ℝ (fun x => fderiv ℝ Φ x w) y v := by
  rw [iteratedFDeriv_two_apply]
  have h1 : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) y) y :=
    ((hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y).hasFDerivAt
  have h2 := h1.clm_apply (hasFDerivAt_const w y)
  rw [h2.fderiv]
  simp

def sumSecondC (Φ : Space → ℂ) (y : Space) : ℂ := ∑ j : Fin 3, iteratedFDeriv ℝ 2 Φ y ![unitVector j, unitVector j]

theorem sumSecond_cp {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) :
    ∃ ψ : ℝ × ℝ → ℂ, Good ψ ∧ ∀ y, sumSecondC (cp χ m) y = cp ψ m y := by
  have gP := good_plus hχ m
  have gM := good_minus hχ m
  have gPM := good_plus gM (m - 1)
  have gMP := good_minus gP (m + 1)
  have gHH := good_height (good_height hχ)
  refine ⟨fun p => (1 / 2 : ℂ) * plusF (minusF χ m) (m - 1) p + (1 / 2 : ℂ) * minusF (plusF χ m) (m + 1) p +
      heightF (heightF χ) p, good_add (good_add (good_smul gPM _) (good_smul gMP _)) gHH, fun y => ?_⟩
  have hcd := cp_cd hχ m
  have dP := (cp_cd gP (m + 1)).differentiable (by simp)
  have dM := (cp_cd gM (m - 1)).differentiable (by simp)
  have e1 : fderiv ℝ (cp (minusF χ m) (m - 1)) y (unitVector 0) +
      Complex.I * fderiv ℝ (cp (minusF χ m) (m - 1)) y (unitVector 1) = cp (plusF (minusF χ m) (m - 1)) m y := by
    have h := congrFun (plus_eq gM (m - 1)) y
    rwa [sub_add_cancel] at h
  have e2 : fderiv ℝ (cp (plusF χ m) (m + 1)) y (unitVector 0) -
      Complex.I * fderiv ℝ (cp (plusF χ m) (m + 1)) y (unitVector 1) = cp (minusF (plusF χ m) (m + 1)) m y := by
    have h := congrFun (minus_eq gP (m + 1)) y
    rwa [add_sub_cancel_right] at h
  have e3 : fderiv ℝ (cp (heightF χ) m) y (unitVector 2) = cp (heightF (heightF χ)) m y :=
    congrFun (height_eq (good_height hχ) m) y
  have e4 : cp (fun p => (1 / 2 : ℂ) * plusF (minusF χ m) (m - 1) p + (1 / 2 : ℂ) * minusF (plusF χ m) (m + 1) p +
      heightF (heightF χ) p) m y = (1 / 2 : ℂ) * cp (plusF (minusF χ m) (m - 1)) m y +
      (1 / 2 : ℂ) * cp (minusF (plusF χ m) (m + 1)) m y + cp (heightF (heightF χ)) m y := by
    simp only [cp]; ring
  rw [sumSecondC, Fin.sum_univ_three, second hcd, second hcd, second hcd, d0_cp hχ m, d1_cp hχ m, height_eq hχ m,
    fd_comb dP dM, fd_comb dP dM, e3, e4, ← e1, ← e2]
  ring

theorem wave_int (j : ℤ) (hj : j ≠ 0) : ∫ θ in (0 : ℝ)..(2 * Real.pi), wave j θ = 0 := by
  have hc : (j : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
  have hfun : wave j = fun θ : ℝ => Complex.exp ((j : ℂ) * Complex.I * (θ : ℂ)) := by
    funext θ; unfold wave; ring_nf
  rw [hfun, integral_exp_mul_complex hc]
  have h2 : Complex.exp ((j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = Complex.exp ((j : ℂ) * Complex.I * ((0 : ℝ) : ℂ)) := by
    rw [show (j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = (j : ℂ) * Complex.I * ((0 : ℝ) : ℂ) + (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h2, sub_self, zero_div]

theorem wave_ii (j : ℤ) (a b : ℝ) : IntervalIntegrable (wave j) volume a b :=
  (wave_cd j).continuous.intervalIntegrable _ _

theorem two_sum_mode {S : Finset ℤ} {e₁ e₂ : ℤ → ℤ} {a b : ℤ → ℂ} {f : ℝ → ℂ}
    (hf : ∀ θ, f θ = ∑ n ∈ S, (a n * wave (e₁ n) θ + b n * wave (e₂ n) θ)) {k : ℤ}
    (h1 : k ∉ S.image e₁) (h2 : k ∉ S.image e₂) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), wave (-k) θ * f θ = 0 := by
  have hpt : ∀ θ, wave (-k) θ * f θ = ∑ n ∈ S, (a n * wave (e₁ n - k) θ + b n * wave (e₂ n - k) θ) := by
    intro θ
    rw [hf θ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [sub_eq_neg_add, sub_eq_neg_add, ← wave_mul, ← wave_mul]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum (fun n _ => ((wave_ii _ _ _).const_mul _).add ((wave_ii _ _ _).const_mul _))]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [intervalIntegral.integral_add ((wave_ii _ _ _).const_mul _) ((wave_ii _ _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    wave_int _ (sub_ne_zero.2 fun h => h1 (Finset.mem_image.2 ⟨n, hn, h⟩)),
    wave_int _ (sub_ne_zero.2 fun h => h2 (Finset.mem_image.2 ⟨n, hn, h⟩))]
  ring

theorem wave_conj (n : ℤ) (θ : ℝ) : (starRingEnd ℂ) (wave n θ) = wave (-n) θ := by
  unfold wave
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

theorem re_mode {S : Finset ℤ} {a : ℤ → ℂ} {g : ℝ → ℂ} (hg : ∀ θ, g θ = ∑ n ∈ S, a n * wave n θ) {k : ℤ}
    (hk : k ∉ S ∪ S.image (fun n => -n)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), wave (-k) θ * (((g θ).re : ℝ) : ℂ) = 0 := by
  refine two_sum_mode (e₁ := id) (e₂ := fun n => -n) (a := fun n => a n / 2)
    (b := fun n => (starRingEnd ℂ) (a n) / 2) (fun θ => ?_) (by simpa using fun h => hk (Finset.mem_union_left _ h))
    (fun h => hk (Finset.mem_union_right _ h))
  rw [Complex.re_eq_add_conj, hg θ, map_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, wave_conj]; simp only [id]; ring

theorem im_mode {S : Finset ℤ} {a : ℤ → ℂ} {g : ℝ → ℂ} (hg : ∀ θ, g θ = ∑ n ∈ S, a n * wave n θ) {k : ℤ}
    (hk : k ∉ S ∪ S.image (fun n => -n)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), wave (-k) θ * (((g θ).im : ℝ) : ℂ) = 0 := by
  have hg' : ∀ θ, (-Complex.I * g θ) = ∑ n ∈ S, (-Complex.I * a n) * wave n θ := by
    intro θ; rw [hg θ, Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  have := re_mode hg' hk
  simpa using this

end Breakdown.FracInternal.RingModeWeak


namespace Breakdown.FracInternal.RingModeWeak

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.SteadyCert
open Breakdown.CellCert.CellEnergy.Internal.CircleWeak

theorem loc_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → E} (hf : LocallyIntegrable f volume) (T : E →L[ℝ] F) :
    LocallyIntegrable (fun y => T (f y)) volume :=
  locallyIntegrable_iff.2 fun _ hK => T.integrable_comp (hf.integrableOn_isCompact hK)

theorem loc_ofReal {f : Space → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y => (f y : ℂ)) volume :=
  locallyIntegrable_iff.2 fun _ hK => (hf.integrableOn_isCompact hK).ofReal

theorem loc_coord {L : Space → Space} (hL : LocallyIntegrable L volume) (i : Fin 3) :
    LocallyIntegrable (fun y => L y i) volume :=
  loc_comp hL (EuclideanSpace.proj i)

theorem cpF_int {F : Space → ℂ} (hF : LocallyIntegrable F volume) {ψ : ℝ × ℝ → ℂ} (hψ : Good ψ) (m : ℤ) :
    Integrable (fun y => cp ψ m y * F y) := by
  have := hF.integrable_smul_left_of_hasCompactSupport (cp_cd hψ m).continuous (cp_csupp hψ m)
  simpa [smul_eq_mul] using this

theorem int_cp_zero {F : Space → ℂ} (hF : LocallyIntegrable F volume) {ψ : ℝ × ℝ → ℂ} (hψ : Good ψ) (m : ℤ)
    (h : ∀ r z : ℝ, 0 < r → ∫ θ in (0 : ℝ)..(2 * Real.pi), wave m θ * F (cylPoint r θ z) = 0) :
    ∫ y, cp ψ m y * F y = 0 := by
  rw [Breakdown.CellCert.CellFormula.cylChange _ (cpF_int hF hψ m)]
  refine (setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun q hq => ?_).trans
    (integral_zero _ _)
  have hq1 : 0 < q.1 := hq.1
  have e : ∀ θ, cp ψ m (cylPoint q.1 θ q.2) * F (cylPoint q.1 θ q.2) =
      ψ q * (wave m θ * F (cylPoint q.1 θ q.2)) := by
    intro θ; rw [cp_cyl ψ m hq1]; ring
  simp only [e, intervalIntegral.integral_const_mul, h q.1 q.2 hq1, mul_zero]

theorem int_two_zero {F : Space → ℂ} (hF : LocallyIntegrable F volume) {χA χB : ℝ × ℝ → ℂ} (gA : Good χA)
    (gB : Good χB) (mA mB : ℤ) (c d e : ℂ) (hA : ∫ y, cp χA mA y * F y = 0) (hB : ∫ y, cp χB mB y * F y = 0) :
    ∫ y, (c * (d * cp χA mA y + e * cp χB mB y)) * F y = 0 := by
  have e1 : (fun y => (c * (d * cp χA mA y + e * cp χB mB y)) * F y) =
      fun y => (c * d) * (cp χA mA y * F y) + (c * e) * (cp χB mB y * F y) := by
    funext y; ring
  rw [e1, integral_add ((cpF_int hF gA mA).const_mul _) ((cpF_int hF gB mB).const_mul _),
    integral_const_mul, integral_const_mul, hA, hB]
  ring

def kernW (m : ℤ) (F : Space → ℝ) (y : Space) : ℂ := wave m (Complex.arg (plane y)) * (F y : ℂ)

theorem good_real {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) : Good (fun p => (χ p : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp hχ, hχc.comp_left Complex.ofReal_zero,
    fun p hp => (hsub (tsupport_comp_subset Complex.ofReal_zero χ hp)).1⟩

theorem mode_of_probe {F : Space → ℝ} (hF : LocallyIntegrable F volume) (m : ℤ)
    (h : ∀ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) →
      ∫ y, cp (fun p => (χ p : ℂ)) m y * (F y : ℂ) = 0) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      ∫ θ in (0 : ℝ)..(2 * Real.pi), wave m θ * (F (cylPoint p.1 θ p.2) : ℂ) = 0 := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hk : ∀ R, IntegrableOn (kernW m F) (Metric.closedBall 0 R) := by
    intro R
    obtain ⟨C, hC⟩ := bdd_of (wave_cd m).continuous
    exact ((hF.integrableOn_isCompact (isCompact_closedBall _ _)).ofReal).bdd_mul
      (meas_of (wave_cd m).continuous) (Eventually.of_forall hC)
  have hLoc : LocallyIntegrableOn (fun q : ℝ × ℝ => q.1 • ∫ θ in (0 : ℝ)..(2 * Real.pi),
      kernW m F (cylPoint q.1 θ q.2)) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hKc
    obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
    have hI := (cyl_exchange ((integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (hk (3 * R)))).2
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
  · filter_upwards [hZ] with p hp hp1
    have h0 := hp ⟨hp1, mem_univ _⟩
    have h0' : ∫ θ in (0 : ℝ)..(2 * Real.pi), kernW m F (cylPoint p.1 θ p.2) = 0 :=
      (smul_eq_zero.1 h0).resolve_left hp1.ne'
    rw [← h0']
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [kernW, w_circle (wave_per m) hp1]
  · intro χ hχ hχc hsub
    have hg := good_real hχ hχc hsub
    have E := h χ hχ hχc hsub
    rw [Breakdown.CellCert.CellFormula.cylChange _ (cpF_int (loc_ofReal hF) hg m)] at E
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))]
    · refine Eq.trans ?_ E
      refine setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun q hq => ?_
      have hq1 : 0 < q.1 := hq.1
      have e1 : ∀ θ, kernW m F (cylPoint q.1 θ q.2) = wave m θ * (F (cylPoint q.1 θ q.2) : ℂ) := by
        intro θ; simp only [kernW, w_circle (wave_per m) hq1]
      have e2 : ∀ θ, cp (fun p => (χ p : ℂ)) m (cylPoint q.1 θ q.2) * (F (cylPoint q.1 θ q.2) : ℂ) =
          (χ q : ℂ) * (wave m θ * (F (cylPoint q.1 θ q.2) : ℂ)) := by
        intro θ; rw [cp_cyl _ m hq1]; ring
      simp only [e1, e2, intervalIntegral.integral_const_mul, Complex.real_smul]
      ring
    · intro q hq
      have : χ q = 0 := image_eq_zero_of_notMem_tsupport (fun h => hq (hsub h))
      simp [this]

theorem comp_mode {S : Finset ℤ} {X : Space → Space} (hX : GivenFields.IsRingTrigSum S X) (i : Fin 3) {k : ℤ}
    (hk : k ∉ S ∪ S.image (fun n => -n)) (r z : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), wave (-k) θ * ((X (cylPoint r θ z) i : ℝ) : ℂ) = 0 := by
  obtain ⟨a, b, h⟩ := hX r z
  have ha : ∀ θ, Reduction.horizontalPart X (cylPoint r θ z) = ∑ n ∈ S, a n * wave n θ := fun θ => (h θ).1
  have hb : ∀ θ, Reduction.verticalPart X (cylPoint r θ z) = ∑ n ∈ S, b n * wave n θ := fun θ => (h θ).2
  fin_cases i
  · have := re_mode ha hk; simpa [Reduction.horizontalPart] using this
  · have := im_mode ha hk; simpa [Reduction.horizontalPart] using this
  · have := re_mode hb hk; simpa [Reduction.verticalPart] using this

theorem exp_wave (k : ℤ) (θ : ℝ) : Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) = wave (-k) θ := by
  unfold wave; push_cast; ring_nf

theorem cplx {f g : Space → ℂ} (hf : Integrable f) (hg : Integrable g) (hre : ∫ y, (f y).re = ∫ y, (g y).re)
    (him : ∫ y, (f y).im = ∫ y, (g y).im) : ∫ y, f y = ∫ y, g y :=
  Complex.ext (by rw [re_int hf, re_int hg, hre]) (by rw [im_int hf, im_int hg, him])

theorem re_cd {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (fun y => (Φ y).re) :=
  Complex.reCLM.contDiff.comp hΦ

theorem im_cd {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (fun y => (Φ y).im) :=
  Complex.imCLM.contDiff.comp hΦ

theorem fd_re {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (y v : Space) :
    fderiv ℝ (fun y => (Φ y).re) y v = (fderiv ℝ Φ y v).re := by
  have h : HasFDerivAt (fun y => (Φ y).re) (Complex.reCLM.comp (fderiv ℝ Φ y)) y :=
    Complex.reCLM.hasFDerivAt.comp y ((hΦ.differentiable (by simp)) y).hasFDerivAt
  rw [h.fderiv]; rfl

theorem fd_im {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (y v : Space) :
    fderiv ℝ (fun y => (Φ y).im) y v = (fderiv ℝ Φ y v).im := by
  have h : HasFDerivAt (fun y => (Φ y).im) (Complex.imCLM.comp (fderiv ℝ Φ y)) y :=
    Complex.imCLM.hasFDerivAt.comp y ((hΦ.differentiable (by simp)) y).hasFDerivAt
  rw [h.fderiv]; rfl

theorem it_re {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (y : Space) (v : Fin 2 → Space) :
    iteratedFDeriv ℝ 2 (fun y => (Φ y).re) y v = (iteratedFDeriv ℝ 2 Φ y v).re := by
  have h := Complex.reCLM.iteratedFDeriv_comp_left (x := y) hΦ.contDiffAt (i := 2) (WithTop.coe_le_coe.2 le_top)
  have h' := congrArg (fun T => T v) h
  rw [show (fun y => (Φ y).re) = (Complex.reCLM ∘ Φ) from rfl]
  simpa using h'

theorem it_im {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (y : Space) (v : Fin 2 → Space) :
    iteratedFDeriv ℝ 2 (fun y => (Φ y).im) y v = (iteratedFDeriv ℝ 2 Φ y v).im := by
  have h := Complex.imCLM.iteratedFDeriv_comp_left (x := y) hΦ.contDiffAt (i := 2) (WithTop.coe_le_coe.2 le_top)
  have h' := congrArg (fun T => T v) h
  rw [show (fun y => (Φ y).im) = (Complex.imCLM ∘ Φ) from rfl]
  simpa using h'

theorem inner_unit (v : Space) (i : Fin 3) : inner ℝ v (unitVector i) = v i := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem sumSecond_smul {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (i : Fin 3) (y : Space) :
    sumSecondPartialsAt (fun y => ψ y • unitVector i) y =
      (∑ j : Fin 3, iteratedFDeriv ℝ 2 ψ y ![unitVector j, unitVector j]) • unitVector i := by
  have h : ∀ v, iteratedFDeriv ℝ 2 (fun y => ψ y • unitVector i) y v = iteratedFDeriv ℝ 2 ψ y v • unitVector i := by
    intro v
    have h1 := (ContinuousLinearMap.toSpanSingleton ℝ (unitVector i)).iteratedFDeriv_comp_left (x := y)
      hψ.contDiffAt (i := 2) (WithTop.coe_le_coe.2 le_top)
    have h2 := congrArg (fun T => T v) h1
    simpa [Function.comp_def] using h2
  simp only [sumSecondPartialsAt, h, Finset.sum_smul]

theorem weak_neg_c {X L : Space → Space} (hw : Reduction.IsWeakNegTraceOf X L) (i : Fin 3) {Φ : Space → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) (hf : Integrable (fun y => sumSecondC Φ y * (X y i : ℂ)))
    (hg : Integrable (fun y => Φ y * (L y i : ℂ))) :
    ∫ y, sumSecondC Φ y * (X y i : ℂ) = -∫ y, Φ y * (L y i : ℂ) := by
  have real : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y, (∑ j : Fin 3, iteratedFDeriv ℝ 2 ψ y ![unitVector j, unitVector j]) * X y i = ∫ y, -(ψ y * L y i) := by
    intro ψ hψ hψc
    have hT : IsTestVectorField (fun y => ψ y • unitVector i) := by
      refine ⟨hψ.smul contDiff_const, hψc.mono fun y hy => ?_⟩
      simp only [Function.mem_support] at hy ⊢
      intro h; exact hy (by simp [h])
    have E := hw _ hT
    simp only [sumSecond_smul hψ, inner_neg_right, real_inner_smul_right, inner_unit] at E
    rw [integral_neg, ← E, integral_neg, neg_neg]
  rw [← integral_neg]
  refine cplx hf hg.neg ?_ ?_
  · have R := real _ (re_cd hΦ) (hΦc.comp_left Complex.zero_re)
    simp only [it_re hΦ] at R
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re, sumSecondC,
      Complex.re_sum]
    exact R
  · have R := real _ (im_cd hΦ) (hΦc.comp_left Complex.zero_im)
    simp only [it_im hΦ] at R
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_add, Complex.neg_im, sumSecondC,
      Complex.im_sum]
    exact R

theorem weak_grad_c {q : Space → ℝ} {Q : Space → Space} (hw : Reduction.IsWeakScalarGradientOf q Q) (j : Fin 3)
    {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (hf : Integrable (fun y => fderiv ℝ Φ y (unitVector j) * (q y : ℂ)))
    (hg : Integrable (fun y => Φ y * (Q y j : ℂ))) :
    ∫ y, fderiv ℝ Φ y (unitVector j) * (q y : ℂ) = -∫ y, Φ y * (Q y j : ℂ) := by
  have real : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y, fderiv ℝ ψ y (unitVector j) * q y = ∫ y, -(ψ y * Q y j) := by
    intro ψ hψ hψc
    have E := hw ψ ⟨hψ, hψc⟩ j
    simp only [inner_unit] at E
    rw [E, integral_neg]
  rw [← integral_neg]
  refine cplx hf hg.neg ?_ ?_
  · have R := real _ (re_cd hΦ) (hΦc.comp_left Complex.zero_re)
    simp only [fd_re hΦ] at R
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re]
    exact R
  · have R := real _ (im_cd hΦ) (hΦc.comp_left Complex.zero_im)
    simp only [fd_im hΦ] at R
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_add, Complex.neg_im]
    exact R

theorem fd_smul {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (i : Fin 3) (y : Space) :
    fderiv ℝ (fun y => ψ y • unitVector i) y = (ContinuousLinearMap.toSpanSingleton ℝ (unitVector i)).comp (fderiv ℝ ψ y) := by
  have h : HasFDerivAt (fun y => ψ y • unitVector i)
      ((ContinuousLinearMap.toSpanSingleton ℝ (unitVector i)).comp (fderiv ℝ ψ y)) y :=
    (ContinuousLinearMap.toSpanSingleton ℝ (unitVector i)).hasFDerivAt.comp y
      ((hψ.differentiable (by simp)) y).hasFDerivAt
  exact h.fderiv

theorem weak_div_c {Y : Space → (Space →L[ℝ] Space)} {L : Space → Space} (hw : Reduction.IsWeakMatrixDivergenceOf Y L)
    (i : Fin 3) {Φ : Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (hf : Integrable (fun y => ∑ a : Fin 3, fderiv ℝ Φ y (unitVector a) * ((Y y (unitVector a)) i : ℂ)))
    (hg : Integrable (fun y => Φ y * (L y i : ℂ))) :
    ∫ y, ∑ a : Fin 3, fderiv ℝ Φ y (unitVector a) * ((Y y (unitVector a)) i : ℂ) = -∫ y, Φ y * (L y i : ℂ) := by
  have real : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y, ∑ a : Fin 3, fderiv ℝ ψ y (unitVector a) * (Y y (unitVector a)) i = ∫ y, -(ψ y * L y i) := by
    intro ψ hψ hψc
    have hT : IsTestVectorField (fun y => ψ y • unitVector i) := by
      refine ⟨hψ.smul contDiff_const, hψc.mono fun y hy => ?_⟩
      simp only [Function.mem_support] at hy ⊢
      intro h; exact hy (by simp [h])
    have E := hw _ hT
    simp only [fd_smul hψ, entryInner, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      real_inner_smul_left, real_inner_smul_right, inner_unit] at E
    rw [integral_neg, ← E]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [real_inner_comm, inner_unit]
  rw [← integral_neg]
  refine cplx hf hg.neg ?_ ?_
  · have R := real _ (re_cd hΦ) (hΦc.comp_left Complex.zero_re)
    simp only [fd_re hΦ] at R
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re,
      Complex.re_sum]
    exact R
  · have R := real _ (im_cd hΦ) (hΦc.comp_left Complex.zero_im)
    simp only [fd_im hΦ] at R
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_add, Complex.neg_im,
      Complex.im_sum]
    exact R

theorem shift_mem {S : Finset ℤ} {k j : ℤ} (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (h : k - j ∈ S) :
    k ∈ S + {-1, 0, 1} := by
  have := Finset.add_mem_add h hj
  rwa [sub_add_cancel] at this

theorem d0' {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) (y : Space) : fderiv ℝ (cp χ m) y (unitVector 0) =
    (1 / 2 : ℂ) * (1 * cp (plusF χ m) (m + 1) y + 1 * cp (minusF χ m) (m - 1) y) := congrFun (d0_cp hχ m) y

theorem d1' {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) (y : Space) : fderiv ℝ (cp χ m) y (unitVector 1) =
    (-(Complex.I / 2)) * (1 * cp (plusF χ m) (m + 1) y + (-1) * cp (minusF χ m) (m - 1) y) := congrFun (d1_cp hχ m) y

theorem d2' {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) (y : Space) : fderiv ℝ (cp χ m) y (unitVector 2) =
    cp (heightF χ) m y := congrFun (height_eq hχ m) y

theorem d_zero {F : Space → ℂ} (hF : LocallyIntegrable F volume) {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (k : ℤ)
    (h1 : ∀ r z : ℝ, 0 < r → ∫ θ in (0 : ℝ)..(2 * Real.pi), wave (-k + 1) θ * F (cylPoint r θ z) = 0)
    (h0 : ∀ r z : ℝ, 0 < r → ∫ θ in (0 : ℝ)..(2 * Real.pi), wave (-k) θ * F (cylPoint r θ z) = 0)
    (h2 : ∀ r z : ℝ, 0 < r → ∫ θ in (0 : ℝ)..(2 * Real.pi), wave (-k - 1) θ * F (cylPoint r θ z) = 0)
    (a : Fin 3) : ∫ y, fderiv ℝ (cp χ (-k)) y (unitVector a) * F y = 0 := by
  have gP := good_plus hχ (-k)
  have gM := good_minus hχ (-k)
  have hP : ∫ y, cp (plusF χ (-k)) (-k + 1) y * F y = 0 :=
    int_cp_zero hF gP _ h1
  have hM : ∫ y, cp (minusF χ (-k)) (-k - 1) y * F y = 0 :=
    int_cp_zero hF gM _ h2
  fin_cases a
  · show ∫ y, fderiv ℝ (cp χ (-k)) y (unitVector 0) * F y = 0
    simp only [d0' hχ]
    exact int_two_zero hF gP gM (-k + 1) (-k - 1) _ _ _ hP hM
  · show ∫ y, fderiv ℝ (cp χ (-k)) y (unitVector 1) * F y = 0
    simp only [d1' hχ]
    exact int_two_zero hF gP gM (-k + 1) (-k - 1) _ _ _ hP hM
  · show ∫ y, fderiv ℝ (cp χ (-k)) y (unitVector 2) * F y = 0
    simp only [d2' hχ]
    exact int_cp_zero hF (good_height hχ) _ h0

end Breakdown.FracInternal.RingModeWeak


namespace Breakdown.FracInternal.RingModeWeak

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.SteadyCert
open Breakdown.CellCert.CellEnergy.Internal.CircleWeak

theorem dF_int {F : Space → ℂ} (hF : LocallyIntegrable F volume) {χ : ℝ × ℝ → ℂ} (hχ : Good χ) (m : ℤ) (v : Space) :
    Integrable (fun y => fderiv ℝ (cp χ m) y v * F y) := by
  have := hF.integrable_smul_left_of_hasCompactSupport
    (((cp_cd hχ m).continuous_fderiv (by simp)).clm_apply continuous_const) (csupp_fderiv_apply (cp_csupp hχ m) (fun _ => v))
  simpa [smul_eq_mul] using this

end Breakdown.FracInternal.RingModeWeak


namespace Breakdown.FracInternal.RingModeWeak

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.SteadyCert
open Breakdown.CellCert.CellEnergy.Internal.CircleWeak

theorem wave_mode (n : ℤ) (θ : ℝ) : fourier n (θ : AddCircle (2 * Real.pi)) = wave n θ := by
  rw [fourier_coe_apply]
  unfold wave
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem norm_wave (m : ℤ) (θ : ℝ) : ‖wave m θ‖ = 1 := by
  unfold wave
  rw [show (m : ℂ) * (θ : ℂ) * Complex.I = (((m : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem circle_unique {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo (-Real.pi) Real.pi))
    (h : ∀ m : ℤ, ∫ θ in Ioo (-Real.pi) Real.pi, wave m θ * g θ = 0) :
    ∀ᵐ θ ∂(volume.restrict (Ioo (-Real.pi) Real.pi)), g θ = 0 := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hint : ∀ φ : C(AddCircle (2 * Real.pi), ℂ),
      IntegrableOn (fun θ : ℝ => φ θ * g θ) (Ioo (-Real.pi) Real.pi) := by
    intro φ
    exact Integrable.bdd_mul hg ((φ.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))).aestronglyMeasurable)
      (Eventually.of_forall fun θ => φ.norm_coe_le_norm _)
  let Λ : C(AddCircle (2 * Real.pi), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ θ in Ioo (-Real.pi) Real.pi, φ θ * g θ
      map_add' := fun φ ψ => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint φ) (hint ψ)
      map_smul' := fun c φ => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  let Λc := Λ.mkContinuous (∫ θ in Ioo (-Real.pi) Real.pi, ‖g θ‖) fun φ => by
    show ‖∫ θ in Ioo (-Real.pi) Real.pi, φ θ * g θ‖ ≤ _
    refine (norm_integral_le_of_norm_le (hg.norm.const_mul ‖φ‖) (Eventually.of_forall fun θ => ?_)).trans ?_
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm _) (norm_nonneg _)
    · rw [integral_const_mul, mul_comm]
  have hker : ∀ φ, Λc φ = 0 := by
    have hsub : Submodule.span ℂ (range (@fourier (2 * Real.pi))) ≤ LinearMap.ker (Λc : C(AddCircle (2 * Real.pi), ℂ) →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      show ∫ θ in Ioo (-Real.pi) Real.pi, fourier n (θ : AddCircle (2 * Real.pi)) * g θ = 0
      simp only [wave_mode]
      exact h n
    have hcl := Submodule.topologicalClosure_minimal _ hsub Λc.isClosed_ker
    rw [span_fourier_closure_eq_top] at hcl
    intro φ
    exact hcl Submodule.mem_top
  have hZ := (isOpen_Ioo (a := -Real.pi) (b := Real.pi)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hg.locallyIntegrableOn ?_
  · exact (ae_restrict_iff' measurableSet_Ioo).2 hZ
  · intro ψ hψ hψc hsub
    have hz : ∀ θ, θ ∉ Ioo (-Real.pi) Real.pi → ψ θ = 0 := fun θ hθ =>
      image_eq_zero_of_notMem_tsupport (fun h => hθ (hsub h))
    have hend : (fun θ => (ψ θ : ℂ)) (-Real.pi) = (fun θ => (ψ θ : ℂ)) (-Real.pi + 2 * Real.pi) := by
      simp only
      rw [hz _ (fun h => lt_irrefl _ h.1), hz _ (fun h => by linarith [h.2])]
    let φ : C(AddCircle (2 * Real.pi), ℂ) :=
      ⟨AddCircle.liftIco (2 * Real.pi) (-Real.pi) (fun θ => (ψ θ : ℂ)),
        AddCircle.liftIco_continuous hend (Complex.continuous_ofReal.comp hψ.continuous).continuousOn⟩
    have hφ : ∀ θ ∈ Ioo (-Real.pi) Real.pi, φ θ = (ψ θ : ℂ) := by
      intro θ hθ
      have hm : θ ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := ⟨hθ.1.le, by linarith [hθ.2]⟩
      show AddCircle.liftIco (2 * Real.pi) (-Real.pi) (fun θ => (ψ θ : ℂ)) θ = _
      exact AddCircle.liftIco_coe_apply hm
    have E := hker φ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (-Real.pi) Real.pi)
      (fun θ hθ => by simp [hz θ hθ])]
    rw [← E]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    show (ψ θ) • g θ = φ θ * g θ
    rw [hφ θ hθ, Complex.real_smul]

theorem shift_int {f : ℝ → ℂ} (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ = ∫ θ in Ioo (-Real.pi) Real.pi, f θ := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hsh := hf.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at hsh
  rw [hsh, intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo]

theorem wave_ioo (j : ℤ) (hj : j ≠ 0) : ∫ θ in Ioo (-Real.pi) Real.pi, wave j θ = 0 := by
  rw [← shift_int (wave_per j)]; exact wave_int j hj

theorem wave_zero (θ : ℝ) : wave 0 θ = 1 := by simp [wave]

theorem wave_ioo_zero : ∫ θ in Ioo (-Real.pi) Real.pi, wave 0 θ = 2 * Real.pi := by
  simp only [wave_zero, integral_const]
  rw [show (volume.restrict (Ioo (-Real.pi) Real.pi)).real univ = 2 * Real.pi by
    first
    | rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]; ring
    | rw [Measure.real_def, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]; ring]
  simp

theorem wave_add (n : ℤ) (a b : ℝ) : wave n (a + b) = wave n a * wave n b := by
  unfold wave; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem wave_ion (m : ℤ) : IntegrableOn (wave m) (Ioo (-Real.pi) Real.pi) :=
  ((wave_cd m).continuous.integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem re_rep (T : Finset ℤ) (c : ℤ → ℂ) : ∃ a : ℤ → ℂ, ∀ θ : ℝ,
    ((((∑ n ∈ T, c n * wave n θ).re : ℝ) : ℂ)) = ∑ n ∈ T ∪ T.image (fun n => -n), a n * wave n θ := by
  classical
  refine ⟨fun n => (if n ∈ T then c n / 2 else 0) +
    (if n ∈ T.image (fun n => -n) then (starRingEnd ℂ) (c (-n)) / 2 else 0), fun θ => ?_⟩
  have e1 : ∑ n ∈ T ∪ T.image (fun n => -n), (if n ∈ T then c n / 2 else 0) * wave n θ =
      (∑ n ∈ T, c n * wave n θ) / 2 := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 Finset.subset_union_left, Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => by ring
  have e2 : ∑ n ∈ T ∪ T.image (fun n => -n),
      (if n ∈ T.image (fun n => -n) then (starRingEnd ℂ) (c (-n)) / 2 else 0) * wave n θ =
      (∑ n ∈ T, (starRingEnd ℂ) (c n * wave n θ)) / 2 := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 Finset.subset_union_right,
      Finset.sum_image (fun x _ y _ h => neg_injective h), Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, wave_conj, neg_neg]; ring
  rw [Complex.re_eq_add_conj, map_sum]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [e1, e2]; ring

end Breakdown.FracInternal.RingModeWeak

namespace Breakdown.FracInternal.RingModeWeak

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis
open Breakdown.CellCert.CellEnergy.Internal.CircleWeak

theorem wave_cyl (n : ℤ) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    wave n (Complex.arg (plane (cylPoint r θ z))) = wave n θ := w_circle (wave_per n) hr θ z

theorem cyl_per (r z θ : ℝ) : cylPoint r (θ + 2 * Real.pi) z = cylPoint r θ z := by
  simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

end Breakdown.FracInternal.RingModeWeak

namespace Breakdown.CellCert.GivenFields

open Breakdown.FracInternal.RingModeWeak Breakdown.CellCert.CellAnalysis Breakdown.SteadyCert
open Breakdown.CellCert.CellEnergy.Internal.CircleWeak
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem ringModes_unique {T : Finset ℤ} {u : Space → ℝ} (hu : LocallyIntegrable u volume)
    (hT : ∀ k : ℤ, k ∉ T → ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 →
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) *
        ((u (Reduction.ringPoint q.1 θ q.2) : ℝ) : ℂ) = 0) :
    ∃ G : Space → ℝ, (∀ᵐ y ∂volume, G y = u y) ∧ ∃ S : Finset ℤ, ∀ ρ z : ℝ, ∃ a : ℤ → ℂ, ∀ θ : ℝ,
      ((G (Reduction.ringPoint ρ θ z) : ℝ) : ℂ) = ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := by
  classical
  have hsm : StronglyMeasurable (hu.aestronglyMeasurable.mk u) := hu.aestronglyMeasurable.stronglyMeasurable_mk
  have huu : u =ᵐ[volume] hu.aestronglyMeasurable.mk u := hu.aestronglyMeasurable.ae_eq_mk
  set v := hu.aestronglyMeasurable.mk u with hv
  have hvloc : LocallyIntegrable v volume := hu.congr huu
  let coef : ℤ → ℝ × ℝ → ℂ := fun n p => (1 / (2 * Real.pi) : ℂ) *
    ∫ θ in Ioo (-Real.pi) Real.pi, wave (-n) θ * (v (cylPoint p.1 θ p.2) : ℂ)
  have hcoef : ∀ n, Measurable (coef n) := by
    intro n
    have hf : StronglyMeasurable (fun x : (ℝ × ℝ) × ℝ => wave (-n) x.2 * (v (cylPoint x.1.1 x.2 x.1.2) : ℂ)) :=
      (((wave_cd (-n)).continuous.measurable.comp measurable_snd).mul
        (Complex.measurable_ofReal.comp (hsm.measurable.comp cylArg_meas))).stronglyMeasurable
    exact (hf.integral_prod_right' (ν := volume.restrict (Ioo (-Real.pi) Real.pi))).measurable.const_mul _
  let G : Space → ℝ := fun y => if 0 < cylRadius y then
    (∑ n ∈ T, coef n (cylRadius y, y 2) * wave n (Complex.arg (plane y))).re else 0
  have hG : Measurable G := by
    refine Measurable.ite (measurableSet_lt measurable_const radius_cont.measurable) ?_ measurable_const
    refine Complex.measurable_re.comp (Finset.measurable_sum _ fun n _ => ((hcoef n).comp pair_cont.measurable).mul ?_)
    exact (wave_cd n).continuous.measurable.comp (Complex.measurable_arg.comp plane_cd.continuous.measurable)
  have hring : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → ∀ᵐ θ ∂(volume.restrict (Ioo (-Real.pi) Real.pi)),
      G (cylPoint p.1 θ p.2) = v (cylPoint p.1 θ p.2) := by
    have hT2 : ∀ᵐ q : ℝ × ℝ ∂volume, ∀ n : ℤ, n ∉ T → 0 < q.1 →
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) *
          ((u (Reduction.ringPoint q.1 θ q.2) : ℝ) : ℂ) = 0 := by
      rw [ae_all_iff]
      intro n
      by_cases hn : n ∈ T
      · exact Eventually.of_forall fun q h => absurd hn h
      · filter_upwards [hT n hn] with q hq _ using hq
    filter_upwards [hT2, FracInternal.MeshDataAffineModes.ae_ring hvloc,
      FracInternal.MeshDataAffineModes.ae_circle_eq huu] with p hp hI hE hp1
    have hE' := (ae_restrict_iff' measurableSet_Ioo).1 (hE hp1)
    have hIv : IntegrableOn (fun θ => (v (cylPoint p.1 θ p.2) : ℂ)) (Ioo (-Real.pi) Real.pi) := (hI hp1).ofReal
    have hmodes : ∀ n : ℤ, n ∉ T →
        ∫ θ in Ioo (-Real.pi) Real.pi, wave (-n) θ * (v (cylPoint p.1 θ p.2) : ℂ) = 0 := by
      intro n hn
      have h0 := hp n hn hp1
      simp only [exp_wave] at h0
      have h1 : ∫ θ in (0 : ℝ)..(2 * Real.pi), wave (-n) θ * (u (cylPoint p.1 θ p.2) : ℂ) = 0 := h0
      rw [shift_int (fun θ => by simp only [wave_per (-n) θ, cyl_per])] at h1
      rw [← h1]
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [hE'] with θ hθ hmem
      rw [hθ hmem]
    let g : ℝ → ℂ := fun θ => (v (cylPoint p.1 θ p.2) : ℂ) - ∑ n ∈ T, coef n (p.1, p.2) * wave n θ
    have hgI : IntegrableOn g (Ioo (-Real.pi) Real.pi) :=
      hIv.sub (integrable_finset_sum _ fun n _ => (wave_ion n).const_mul _)
    have hall : ∀ m : ℤ, ∫ θ in Ioo (-Real.pi) Real.pi, wave m θ * g θ = 0 := by
      intro m
      have hvm : IntegrableOn (fun θ => wave m θ * (v (cylPoint p.1 θ p.2) : ℂ)) (Ioo (-Real.pi) Real.pi) :=
        Integrable.bdd_mul hIv (wave_cd m).continuous.aestronglyMeasurable
          (Eventually.of_forall fun θ => (norm_wave m θ).le)
      have e : ∀ θ, wave m θ * g θ = wave m θ * (v (cylPoint p.1 θ p.2) : ℂ) -
          ∑ n ∈ T, coef n (p.1, p.2) * wave (m + n) θ := by
        intro θ
        simp only [g]
        rw [mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← wave_mul]; ring
      simp_rw [e]
      rw [integral_sub hvm (integrable_finset_sum _ fun n _ => (wave_ion _).const_mul _),
        integral_finset_sum _ fun n _ => (wave_ion _).const_mul _]
      simp_rw [integral_const_mul]
      by_cases hm : -m ∈ T
      · rw [Finset.sum_eq_single (-m)]
        · rw [show m + -m = 0 by ring, wave_ioo_zero]
          simp only [coef, neg_neg]
          have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
          first
          | (field_simp; done)
          | (field_simp; ring)
        · intro n _ hn
          rw [wave_ioo _ (by intro h; apply hn; omega), mul_zero]
        · intro h; exact absurd hm h
      · rw [Finset.sum_eq_zero fun n hn => by
          rw [wave_ioo _ (by intro h; apply hm; rw [show -m = n by omega]; exact hn), mul_zero], sub_zero]
        have := hmodes (-m) hm
        rwa [neg_neg] at this
    have hz := circle_unique hgI hall
    filter_upwards [hz] with θ hθ
    have hs : ∑ n ∈ T, coef n (p.1, p.2) * wave n θ = (v (cylPoint p.1 θ p.2) : ℂ) := (sub_eq_zero.1 hθ).symm
    simp only [G, radius_cyl hp1, height_cyl, wave_cyl _ hp1, if_pos hp1, hs, Complex.ofReal_re]
  have hGv : ∀ᵐ y ∂volume, G y = v y := by
    have hD : MeasurableSet {y | G y ≠ v y} := (measurableSet_eq_fun hG hsm.measurable).compl
    rw [ae_iff]
    have h1 : ∀ᵐ q ∂muU, cylArg q ∉ {y | G y ≠ v y} := by
      rw [muU_def]
      refine (Measure.ae_prod_iff_ae_ae (p := fun q => cylArg q ∉ {y | G y ≠ v y}) (cylArg_meas hD.compl)).2 ?_
      have hUm : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
      filter_upwards [(ae_restrict_iff' hUm).2 (hring.mono fun p hp hmem => hp hmem.1)] with p hp
      filter_upwards [hp] with θ hθ
      simp only [mem_setOf_eq, not_not]
      exact hθ
    rw [← lintegral_indicator_one hD, ← key]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [h1] with q hq
    have hq' : cylArg q ∉ {y | G y ≠ v y} := hq
    simp [Set.indicator_of_notMem hq']
  refine ⟨G, Filter.EventuallyEq.trans (show G =ᵐ[volume] v from hGv) huu.symm, T ∪ T.image (fun n => -n), fun ρ z => ?_⟩
  have hkey : ∃ c : ℤ → ℂ, ∀ θ, G (cylPoint ρ θ z) = (∑ n ∈ T, c n * wave n θ).re := by
    rcases lt_trichotomy ρ 0 with h | h | h
    · have hr : 0 < -ρ := neg_pos.2 h
      refine ⟨fun n => coef n (-ρ, z) * wave n Real.pi, fun θ => ?_⟩
      have e : cylPoint ρ θ z = cylPoint (-ρ) (θ + Real.pi) z := by
        simpa using FracInternal.MeshDataAffineModes.cyl_neg (-ρ) θ z
      simp only [G, e, radius_cyl hr, height_cyl, wave_cyl _ hr, if_pos hr]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [wave_add]; ring
    · refine ⟨0, fun θ => ?_⟩
      subst h
      have : ¬ 0 < cylRadius (cylPoint 0 θ z) := by simp [cylRadius, cylPoint]
      simp only [G, if_neg this]
      simp
    · refine ⟨fun n => coef n (ρ, z), fun θ => ?_⟩
      simp only [G, radius_cyl h, height_cyl, wave_cyl _ h, if_pos h]
  obtain ⟨c, hc⟩ := hkey
  obtain ⟨a, ha⟩ := re_rep T c
  refine ⟨a, fun θ => ?_⟩
  show ((G (cylPoint ρ θ z) : ℝ) : ℂ) = ∑ n ∈ T ∪ T.image (fun n => -n), a n * wave n θ
  rw [hc θ, ha θ]

end Breakdown.CellCert.GivenFields

namespace Breakdown.CellCert.GivenFields

open Breakdown.FracInternal.RingModeWeak Breakdown.CellCert.CellAnalysis Breakdown.SteadyCert

theorem negTrace_ringModes {S : Finset ℤ} {X : Space → Space} (hX : IsRingTrigSum S X)
    (hXloc : LocallyIntegrable X volume) {L : Space → Space} (hLloc : LocallyIntegrable L volume)
    (hL : Reduction.IsWeakNegTraceOf X L) (i : Fin 3) :
    ∀ k : ℤ, k ∉ S ∪ S.image (fun n => -n) → ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 →
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) *
        ((L (Reduction.ringPoint q.1 θ q.2) i : ℝ) : ℂ) = 0 := by
  intro k hk
  have hmode := mode_of_probe (loc_coord hLloc i) (-k) (fun χ hχ hχc hsub => ?_)
  · filter_upwards [hmode] with p hp hp1
    simp only [exp_wave]
    exact hp hp1
  · have hg := good_real hχ hχc hsub
    obtain ⟨ψ, hψ, hssp⟩ := sumSecond_cp hg (-k)
    have hsumSecondf : sumSecondC (cp (fun p => (χ p : ℂ)) (-k)) = cp ψ (-k) := funext hssp
    have hXi := loc_ofReal (loc_coord hXloc i)
    have hLi := loc_ofReal (loc_coord hLloc i)
    have E := weak_neg_c hL i (cp_cd hg (-k)) (cp_csupp hg (-k))
      (by rw [hsumSecondf]; exact cpF_int hXi hψ (-k)) (cpF_int hLi hg (-k))
    have Z : ∫ y, sumSecondC (cp (fun p => (χ p : ℂ)) (-k)) y * (X y i : ℂ) = 0 := by
      rw [hsumSecondf]
      exact int_cp_zero hXi hψ (-k) (fun r z _ => comp_mode hX i hk r z)
    rw [Z, eq_comm, neg_eq_zero] at E
    exact E

theorem scalarGradient_ringModes {S : Finset ℤ} {q : Space → ℝ}
    (hq : ∀ ρ z : ℝ, ∃ a : ℤ → ℂ, ∀ θ : ℝ,
      ((q (Reduction.ringPoint ρ θ z) : ℝ) : ℂ) = ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I))
    (hqloc : LocallyIntegrable q volume) {Q : Space → Space} (hQloc : LocallyIntegrable Q volume)
    (hQ : Reduction.IsWeakScalarGradientOf q Q) (i : Fin 3) :
    ∀ k : ℤ, k ∉ S + {-1, 0, 1} → ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) *
        ((Q (Reduction.ringPoint p.1 θ p.2) i : ℝ) : ℂ) = 0 := by
  intro k hk
  have hqm : ∀ m : ℤ, -m ∉ S → ∀ r z : ℝ, 0 < r →
      ∫ θ in (0 : ℝ)..(2 * Real.pi), wave m θ * (q (cylPoint r θ z) : ℂ) = 0 := by
    intro m hm r z _
    obtain ⟨a, ha⟩ := hq r z
    have h := two_sum_mode (S := S) (e₁ := id) (e₂ := id) (a := a) (b := fun _ => 0)
      (f := fun θ => (q (cylPoint r θ z) : ℂ)) (fun θ => by
        show ((q (Reduction.ringPoint r θ z) : ℝ) : ℂ) = _
        rw [ha θ]; simp [wave]) (k := -m) (by simpa using hm) (by simpa using hm)
    simpa using h
  have c1 : -(-k + 1) ∉ S := fun h => hk (shift_mem (j := 1) (by simp) (by convert h using 1; ring))
  have c0 : -(-k) ∉ S := fun h => hk (shift_mem (j := 0) (by simp) (by convert h using 1; ring))
  have c2 : -(-k - 1) ∉ S := fun h => hk (shift_mem (j := -1) (by simp) (by convert h using 1; ring))
  have hmode := mode_of_probe (loc_coord hQloc i) (-k) (fun χ hχ hχc hsub => ?_)
  · filter_upwards [hmode] with p hp hp1
    simp only [exp_wave]
    exact hp hp1
  · have hg := good_real hχ hχc hsub
    have hqc := loc_ofReal hqloc
    have hQi := loc_ofReal (loc_coord hQloc i)
    have E := weak_grad_c hQ i (cp_cd hg (-k)) (cp_csupp hg (-k)) (dF_int hqc hg (-k) _) (cpF_int hQi hg (-k))
    have Z := d_zero hqc hg k (fun r z hr => hqm _ c1 r z hr) (fun r z hr => hqm _ c0 r z hr)
      (fun r z hr => hqm _ c2 r z hr) i
    rw [Z, eq_comm, neg_eq_zero] at E
    exact E

theorem matrixDivergence_ringModes {S : Finset ℤ} {Y : Space → (Space →L[ℝ] Space)}
    (hY : ∀ j : Fin 3, IsRingTrigSum S (fun y => Y y (unitVector j)))
    (hYloc : LocallyIntegrable Y volume) {L : Space → Space} (hLloc : LocallyIntegrable L volume)
    (hL : Reduction.IsWeakMatrixDivergenceOf Y L) (i : Fin 3) :
    ∀ k : ℤ, k ∉ (S ∪ S.image (fun n => -n)) + {-1, 0, 1} → ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 →
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) *
        ((L (Reduction.ringPoint q.1 θ q.2) i : ℝ) : ℂ) = 0 := by
  intro k hk
  have c1 : k - 1 ∉ S ∪ S.image (fun n => -n) := fun h => hk (shift_mem (j := 1) (by simp) h)
  have c0 : k ∉ S ∪ S.image (fun n => -n) := fun h => hk (shift_mem (j := 0) (by simp) (by rwa [sub_zero]))
  have c2 : k + 1 ∉ S ∪ S.image (fun n => -n) :=
    fun h => hk (shift_mem (j := -1) (by simp) (by rwa [sub_neg_eq_add]))
  have hYa : ∀ a : Fin 3, LocallyIntegrable (fun y => ((Y y (unitVector a) i : ℝ) : ℂ)) volume := fun a =>
    loc_ofReal (loc_comp hYloc ((EuclideanSpace.proj i).comp (ContinuousLinearMap.apply ℝ Space (unitVector a))))
  have hmode := mode_of_probe (loc_coord hLloc i) (-k) (fun χ hχ hχc hsub => ?_)
  · filter_upwards [hmode] with p hp hp1
    simp only [exp_wave]
    exact hp hp1
  · have hg := good_real hχ hχc hsub
    have hLi := loc_ofReal (loc_coord hLloc i)
    have hterm : ∀ a : Fin 3, ∫ y, fderiv ℝ (cp (fun p => (χ p : ℂ)) (-k)) y (unitVector a) *
        ((Y y (unitVector a) i : ℝ) : ℂ) = 0 := by
      intro a
      refine d_zero (hYa a) hg k (fun r z _ => ?_) (fun r z _ => comp_mode (hY a) i c0 r z) (fun r z _ => ?_) a
      · have h := comp_mode (hY a) i c1 r z
        rwa [show -(k - 1) = -k + 1 by ring] at h
      · have h := comp_mode (hY a) i c2 r z
        rwa [show -(k + 1) = -k - 1 by ring] at h
    have hf : Integrable (fun y => ∑ a : Fin 3, fderiv ℝ (cp (fun p => (χ p : ℂ)) (-k)) y (unitVector a) *
        ((Y y (unitVector a) i : ℝ) : ℂ)) :=
      integrable_finset_sum _ fun a _ => dF_int (hYa a) hg (-k) _
    have E := weak_div_c hL i (cp_cd hg (-k)) (cp_csupp hg (-k)) hf (cpF_int hLi hg (-k))
    rw [integral_finset_sum _ fun a _ => dF_int (hYa a) hg (-k) _, Finset.sum_eq_zero fun a _ => hterm a,
      eq_comm, neg_eq_zero] at E
    exact E

end Breakdown.CellCert.GivenFields
